/* SPDX-License-Identifier: GPL-2.0 */

#include <assert.h>
#include <errno.h>
#include <getopt.h>
#include <locale.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <inttypes.h>

#include <sys/resource.h>

#include <bpf/bpf.h>
#include <xdp/xsk.h>
#include <xdp/libxdp.h>

#include <arpa/inet.h>
#include <net/if.h>
#include <linux/if_link.h>
#include <linux/if_ether.h>
#include <linux/ip.h>
#include <linux/ipv6.h>
#include <linux/icmpv6.h>
#include <linux/udp.h>
#include <netinet/in.h>

#include "../common/common_params.h"
#include "../common/common_user_bpf_xdp.h"
#include "../common/common_libbpf.h"

#define FRAME_SCALE_FACTOR 2
#define TX_RING_SCALE_FACTOR 1
#define BATCH_SCALE_FACTOR 1

#define NUM_FRAMES         (FRAME_SCALE_FACTOR * 4096)
#define FRAME_SIZE         XSK_UMEM__DEFAULT_FRAME_SIZE
#define RX_BATCH_SIZE      (BATCH_SCALE_FACTOR * 64)
#define INVALID_UMEM_FRAME UINT64_MAX

#define TX_RING_SIZE (TX_RING_SCALE_FACTOR * XSK_RING_PROD__DEFAULT_NUM_DESCS)

static struct xdp_program *prog;
int xsk_map_fd;
bool custom_xsk = false;
struct config cfg = {
	.ifindex   = -1,
	.xsk_bind_flags = XDP_USE_NEED_WAKEUP,
};

struct xsk_umem_info {
	struct xsk_ring_prod fq;
	struct xsk_ring_cons cq;
	struct xsk_umem *umem;
	void *buffer;
};
struct stats_record {
	uint64_t timestamp;
	uint64_t rx_packets;
	uint64_t rx_bytes;
	uint64_t tx_packets;
	uint64_t tx_bytes;
};
struct xsk_socket_info {
	struct xsk_ring_cons rx;
	struct xsk_ring_prod tx;
	struct xsk_umem_info *umem;
	struct xsk_socket *xsk;

	uint64_t umem_frame_addr[NUM_FRAMES];
	uint32_t umem_frame_free;

	uint32_t outstanding_tx;

	struct stats_record stats;
	struct stats_record prev_stats;
};

static bool process_packet(struct xsk_socket_info *xsk, uint64_t addr, uint32_t len, bool is_initial_rx);

uint64_t total_completed = 0;
uint64_t dropped_no_slots = 0;
uint64_t total_needed = 0;
uint64_t total_allocs = 0;
uint64_t last_batch_size = 0;
uint64_t max_batch_size = 0;
uint64_t max_completed = 0;
uint64_t recycle_retries = 0;
uint64_t extra_tx_kick = 0;

static inline __u32 xsk_ring_prod__free(struct xsk_ring_prod *r)
{
	r->cached_cons = *r->consumer + r->size;
	return r->cached_cons - r->cached_prod;
}

static const char *__doc__ = "AF_XDP kernel bypass example\n";

static const struct option_wrapper long_options[] = {

	{{"help",	 no_argument,		NULL, 'h' },
	 "Show help", false},

	{{"dev",	 required_argument,	NULL, 'd' },
	 "Operate on device <ifname>", "<ifname>", true},

	{{"skb-mode",	 no_argument,		NULL, 'S' },
	 "Install XDP program in SKB (AKA generic) mode"},

	{{"native-mode", no_argument,		NULL, 'N' },
	 "Install XDP program in native mode"},

	{{"auto-mode",	 no_argument,		NULL, 'A' },
	 "Auto-detect SKB or native mode"},

	{{"force",	 no_argument,		NULL, 'F' },
	 "Force install, replacing existing program on interface"},

	{{"copy",        no_argument,		NULL, 'c' },
	 "Force copy mode"},

	{{"zero-copy",	 no_argument,		NULL, 'z' },
	 "Force zero-copy mode"},

	{{"queue",	 required_argument,	NULL, 'Q' },
	 "Configure interface receive queue for AF_XDP, default=0"},

	{{"poll-mode",	 no_argument,		NULL, 'p' },
	 "Use the poll() API waiting for packets to arrive"},

	{{"quiet",	 no_argument,		NULL, 'q' },
	 "Quiet mode (no output)"},

	{{"filename",    required_argument,	NULL,  1  },
	 "Load program from <file>", "<file>"},

	{{"progname",	 required_argument,	NULL,  2  },
	 "Load program from function <name> in the ELF file", "<name>"},

	{{0, 0, NULL,  0 }, NULL, false}
};

static bool global_exit;

static struct xsk_umem_info *configure_xsk_umem(void *buffer, uint64_t size)
{
	struct xsk_umem_info *umem;
	int ret;

	umem = calloc(1, sizeof(*umem));
	if (!umem)
		return NULL;

	ret = xsk_umem__create(&umem->umem, buffer, size, &umem->fq, &umem->cq,
			       NULL);
	if (ret) {
		errno = -ret;
		return NULL;
	}

	umem->buffer = buffer;
	return umem;
}

static uint64_t xsk_alloc_umem_frame(struct xsk_socket_info *xsk)
{
	uint64_t frame;
	if (xsk->umem_frame_free == 0)
		return INVALID_UMEM_FRAME;

	frame = xsk->umem_frame_addr[--xsk->umem_frame_free];
	xsk->umem_frame_addr[xsk->umem_frame_free] = INVALID_UMEM_FRAME;
	return frame;
}

static void xsk_free_umem_frame(struct xsk_socket_info *xsk, uint64_t frame)
{
	assert(xsk->umem_frame_free < NUM_FRAMES);

	xsk->umem_frame_addr[xsk->umem_frame_free++] = frame;
}

static uint64_t xsk_umem_free_frames(struct xsk_socket_info *xsk)
{
	return xsk->umem_frame_free;
}

static struct xsk_socket_info *xsk_configure_socket(struct config *cfg,
						    struct xsk_umem_info *umem)
{
	struct xsk_socket_config xsk_cfg;
	struct xsk_socket_info *xsk_info;
	uint32_t idx;
	int i;
	int ret;
	uint32_t prog_id;

	xsk_info = calloc(1, sizeof(*xsk_info));
	if (!xsk_info)
		return NULL;

	xsk_info->umem = umem;
	xsk_cfg.rx_size = XSK_RING_CONS__DEFAULT_NUM_DESCS;
	xsk_cfg.tx_size = TX_RING_SIZE;
	xsk_cfg.xdp_flags = cfg->xdp_flags;
	xsk_cfg.bind_flags = cfg->xsk_bind_flags;
	xsk_cfg.libbpf_flags = (custom_xsk) ? XSK_LIBBPF_FLAGS__INHIBIT_PROG_LOAD: 0;
	ret = xsk_socket__create(&xsk_info->xsk, cfg->ifname,
				 cfg->xsk_if_queue, umem->umem, &xsk_info->rx,
				 &xsk_info->tx, &xsk_cfg);
	if (ret)
		goto error_exit;

	if (custom_xsk) {
		ret = xsk_socket__update_xskmap(xsk_info->xsk, xsk_map_fd);
		if (ret)
			goto error_exit;
	} else {
		/* Getting the program ID must be after the xdp_socket__create() call */
		if (bpf_xdp_query_id(cfg->ifindex, cfg->xdp_flags, &prog_id))
			goto error_exit;
	}

	/* Initialize umem frame allocation */
	for (i = 0; i < NUM_FRAMES; i++)
		xsk_info->umem_frame_addr[i] = i * FRAME_SIZE;

	xsk_info->umem_frame_free = NUM_FRAMES;

	/* Stuff the receive path with buffers, we assume we have enough */
	ret = xsk_ring_prod__reserve(&xsk_info->umem->fq,
				     XSK_RING_PROD__DEFAULT_NUM_DESCS,
				     &idx);

	if (ret != XSK_RING_PROD__DEFAULT_NUM_DESCS)
		goto error_exit;

	for (i = 0; i < XSK_RING_PROD__DEFAULT_NUM_DESCS; i ++)
		*xsk_ring_prod__fill_addr(&xsk_info->umem->fq, idx++) =
			xsk_alloc_umem_frame(xsk_info);

	xsk_ring_prod__submit(&xsk_info->umem->fq,
			      XSK_RING_PROD__DEFAULT_NUM_DESCS);

	return xsk_info;

error_exit:
	errno = -ret;
	return NULL;
}

static void complete_tx(struct xsk_socket_info *xsk)
{
	unsigned int completed;
	uint32_t idx_cq;

#if 0
	if (!xsk->outstanding_tx) {
	//	printf("No outstanding\n");
		return;
	}
#endif
#if 0 // Moved to where we submit descriptors
	if (xsk_ring_prod__needs_wakeup(&xsk->tx)) {
		printf("Sendto");
		sendto(xsk_socket__fd(xsk->xsk), NULL, 0, MSG_DONTWAIT, NULL, 0);
	}
#endif
	/* Collect/free completed TX buffers */
	completed = xsk_ring_cons__peek(&xsk->umem->cq,
					XSK_RING_CONS__DEFAULT_NUM_DESCS,
					&idx_cq);

	if (completed > 0) {
#if 1
        for (int i = 0; i < completed; i++) {
			xsk_free_umem_frame(xsk,
				*xsk_ring_cons__comp_addr(&xsk->umem->cq,
										  idx_cq++));
		}
		total_completed += completed;
		if (max_completed < completed) {
			max_completed = completed;
		}
#else
		int newly_sent = 0;
		for (int i = 0; i < completed; i++) {
			uint64_t addr = *xsk_ring_cons__comp_addr(&xsk->umem->cq, idx_cq++);
			uint32_t len = 1512;	// HACK: using max length.  We already validated headers are inside packet.
										// TODO: Need a shadow array to store len when we add to TX queue
			//printf("Processing trasmitted packet, addr=%" PRIx64 "\n", addr);
			if (!process_packet(xsk, addr, len, false)) {
				//printf("Freeing transmitted packet\n");
				xsk_free_umem_frame(xsk, addr);
			} else {
				newly_sent++;
			}
		}
		if (newly_sent > 0) {
			sendto(xsk_socket__fd(xsk->xsk), NULL, 0, MSG_DONTWAIT, NULL, 0);
		}
#endif
		xsk_ring_cons__release(&xsk->umem->cq, completed);
		xsk->outstanding_tx -= completed < xsk->outstanding_tx ?
			completed : xsk->outstanding_tx;
		//printf("Done reclaiming transmited packets, xsk->outstanding_tx=%u\n", xsk->outstanding_tx);
	}
}

static inline __sum16 csum16_add(__sum16 csum, __be16 addend)
{
	uint16_t res = (uint16_t)csum;

	res += (__u16)addend;
	return (__sum16)(res + (res < (__u16)addend));
}

static inline __sum16 csum16_sub(__sum16 csum, __be16 addend)
{
	return csum16_add(csum, ~addend);
}

static inline void csum_replace2(__sum16 *sum, __be16 old, __be16 new)
{
	*sum = ~csum16_add(csum16_sub(~(*sum), old), new);
}

bool transmit_packet(struct xsk_socket_info *xsk, uint64_t addr, uint32_t len)
{
	uint32_t tx_idx = 0;
	if (xsk_ring_prod__reserve(&xsk->tx, 1, &tx_idx) != 1) {
		/* No more transmit slots, drop the packet */
		return false;
	}

	xsk_ring_prod__tx_desc(&xsk->tx, tx_idx)->addr = addr;
	xsk_ring_prod__tx_desc(&xsk->tx, tx_idx)->len = len;
	xsk_ring_prod__submit(&xsk->tx, 1);
	xsk->outstanding_tx++;

	xsk->stats.tx_bytes += len;
	xsk->stats.tx_packets++;
	return true;
}

static void duplicate_and_process_packet(struct xsk_socket_info *xsk, uint64_t addr, uint32_t len)
{
	uint64_t frame = xsk_alloc_umem_frame(xsk);
	if (frame == INVALID_UMEM_FRAME) {
		return;
	}
	uint8_t *orig_data = xsk_umem__get_data(xsk->umem->buffer, addr);
	uint8_t *new_data = xsk_umem__get_data(xsk->umem->buffer, frame);
	memcpy(new_data, orig_data, len);
	if (!process_packet(xsk, frame, len, false)) {
		xsk_free_umem_frame(xsk, frame);
		return;
	} // else: Packet was transmitted inside process_packet.
}

typedef struct mcopy {
	in_addr_t  new_addr;
	uint16_t new_port;
} mcopy;

#define NEW_IP 0xc0a80038 // 192.168.0.56
mcopy copy_list[] = {
		{NEW_IP, 8008},
		{NEW_IP, 8009},
		{NEW_IP, 8010},
		{NEW_IP, 8011},
		{NEW_IP, 8012}
		};
#define COPY_LIST_LEN (sizeof(copy_list) / sizeof(copy_list[0]))

static void replace_ip_addr_and_port(struct iphdr *ip, struct udphdr *udp, in_addr_t new_addr, uint16_t new_port) {
	in_addr_t old_addr = ntohl(ip->daddr);
	// Replace IP address
	ip->daddr = htonl(new_addr);
	// Fix the checksum in IP header
	uint32_t csum;
	csum = ~ntohs(ip->check);
	csum -= old_addr;
	csum += new_addr;
	csum = (csum & 0xffff) + (csum >> 16);
	csum = (csum & 0xffff) + (csum >> 16);
	ip->check = ~htons(csum);

	// Fix the checksum in UDP header, including psuedo-header which covers address in IP header
	// If it's zero, then checksumming was skipped, so don't touch it.
	if (udp->check != 0) {
		csum = ~ntohs(udp->check);
		csum -= old_addr;
		csum += new_addr;
		if (new_port != 0) {
			uint16_t old_port = ntohs(udp->dest);
			csum -= old_port;
			csum += new_port;
			udp->dest = htons(new_port);
		}
		csum = (csum & 0xffff) + (csum >> 16);
		csum = (csum & 0xffff) + (csum >> 16);
		udp->check = ~htons(csum);
	} else {
		if (new_port != 0) {
			udp->dest = htons(new_port);
		}
	}
}

static bool multicopy_packet(struct xsk_socket_info *xsk, uint64_t addr, uint32_t len)
{
	unsigned int retries_remaining = 10000;

retry_reserve:
	// First, see if there are enough tx descriptors to make all copies
	unsigned int needed = xsk_prod_nb_free(&xsk->tx, TX_RING_SIZE / 4);
	//printf("needed: %d", needed);
	if (needed < (TX_RING_SIZE / 8)) {
		// Kick tx, in case it is stuck
		sendto(xsk_socket__fd(xsk->xsk), NULL, 0, MSG_DONTWAIT, NULL, 0);
		extra_tx_kick++;
	}
	if (needed < COPY_LIST_LEN) {
		if (retries_remaining > 0) {
			retries_remaining--;

			// Recycle completion list
			complete_tx(xsk);
			recycle_retries++;
			goto retry_reserve;
		}
	}
	if (needed < COPY_LIST_LEN) {
		/* No more transmit slots, drop the packet */
		//printf("Dropping, no more slots\n");
		dropped_no_slots++;
		return false;
	}
	if (needed > COPY_LIST_LEN) {
		needed = COPY_LIST_LEN;
	}
	total_needed += needed;
	uint8_t *pkt = xsk_umem__get_data(xsk->umem->buffer, addr);
	struct ethhdr *eth = (struct ethhdr *) pkt;
	struct iphdr *ip = (struct iphdr *) (eth + 1);

	// Swap MAC addresses, to send right back
	uint8_t tmp_mac[ETH_ALEN];
	memcpy(tmp_mac, eth->h_dest, ETH_ALEN);
	memcpy(eth->h_dest, eth->h_source, ETH_ALEN);
	memcpy(eth->h_source, tmp_mac, ETH_ALEN);

	// Swap IP addresses (neutral to checksumming) so we have correct source IP; dest will be overwritten.
	in_addr_t temp = ip->saddr;	// network byte order, do not care
	ip->saddr = ip->daddr;
	ip->daddr = temp;

#if 0
	int retry_count = 0;
reallocate:
#endif
	// Allocate all the frames first
	unsigned int allocated = 0;
	uint64_t frames[COPY_LIST_LEN];
	for (int i = 0; i < needed; i++) {
		if (i == 0) {
			frames[i] = addr;
		} else {
			frames[i] = xsk_alloc_umem_frame(xsk);
			if (frames[i] == INVALID_UMEM_FRAME) {
				break;
			}
		}
		allocated++;
	}
	total_allocs += allocated;
	//printf("multicopy packet: allocated=%d\n", allocated);
#if 0
	if (allocated == 0) {
		if (retry_count++ < 2) {
			complete_tx(xsk);
			goto reallocate;
		}
		printf("FAILED TO ALLOCATE\n");
		return false;
	}
#endif
	// Copy and fixup each copy's IP/UDP port
	mcopy *m = copy_list;
	for (int i = 0; i < allocated; i++, m++) {
		uint8_t *pkt_copy = xsk_umem__get_data(xsk->umem->buffer, frames[i]);
		// First packet is the original one.
		if (i > 0) {
			memcpy(pkt_copy, pkt, len);
		}
#if 1 // This is simple now, but if vlan headers or ip6 support is needed, then better to use offsets into copy
		struct ethhdr *eth_copy = (struct ethhdr *) pkt_copy;
		struct iphdr *ip_copy = (struct iphdr *) (eth_copy + 1);
		struct udphdr *udp_copy = (struct udphdr*) (ip_copy + 1);
#else
		struct iphdr *ip_copy = (struct iphdr*)(pkt_copy + ((uint8_t*)ip - pkt));
		struct udphdr *udp_copy = (struct udphdr*)(pkt_copy + ((uint8_t*)udp - pkt));
#endif
		replace_ip_addr_and_port(ip_copy, udp_copy, m->new_addr, m->new_port);
	}

	// Reserve
	uint32_t tx_idx = 0;
	unsigned int reserved = xsk_ring_prod__reserve(&xsk->tx, allocated, &tx_idx);
	if (reserved < allocated) {
		printf("Reserved less than allocation!\n");
	}
	// submit
	for (int i = 0; i < allocated; i++, tx_idx++) {
		xsk_ring_prod__tx_desc(&xsk->tx, tx_idx)->addr = frames[i];
		xsk_ring_prod__tx_desc(&xsk->tx, tx_idx)->len = len;
	}
	xsk_ring_prod__submit(&xsk->tx, allocated);
	xsk->outstanding_tx += allocated;

	xsk->stats.tx_bytes += len * allocated;
	xsk->stats.tx_packets += allocated;

	if (xsk_ring_prod__needs_wakeup(&xsk->tx)) {
		sendto(xsk_socket__fd(xsk->xsk), NULL, 0, MSG_DONTWAIT, NULL, 0);
	}
	return true;
}

static bool process_packet(struct xsk_socket_info *xsk,
			   uint64_t addr, uint32_t len, bool is_initial_rx)
{
	uint8_t *pkt = xsk_umem__get_data(xsk->umem->buffer, addr);
	struct ethhdr *eth = (struct ethhdr *) pkt;
	struct iphdr *ip = (struct iphdr *) (eth + 1);
	struct udphdr *udp = (struct udphdr*) (ip + 1);
#define UPPER_PORT 8011
#define LOWER_PORT 8007

	if (ntohs(eth->h_proto) != ETH_P_IP ||
		len < (sizeof(*eth) + sizeof(*ip) + sizeof(*udp)) ||
		// TODO: Should validate IPv4 IHL and skip if there are any options present
		ntohs(udp->dest) > UPPER_PORT || ntohs(udp->dest) < LOWER_PORT)
	{
		return false;
	}
	return multicopy_packet(xsk, addr, len);
// DEAD CODE NOW:

//	printf("process_packet() handling ip.id=%hu, addr=%" PRIx64 "\n", ip->id, addr);
	if (is_initial_rx) {
		// Swap MAC addresses, to send right back
		uint8_t tmp_mac[ETH_ALEN];
		memcpy(tmp_mac, eth->h_dest, ETH_ALEN);
		memcpy(eth->h_dest, eth->h_source, ETH_ALEN);
		memcpy(eth->h_source, tmp_mac, ETH_ALEN);
	}

	uint32_t csum;
#define SIMPLE_SWAP 0
#if SIMPLE_SWAP
	// Simple swap of ip src/dst, should not need checksum adjustment.
	in_addr_t temp = ip->saddr;	// network byte order, do not care
	ip->saddr = ip->daddr;
	ip->daddr = temp;
#else
	in_addr_t new_ip = 0xc0a80038;	// 192.168.0.56
	in_addr_t old_ip = ntohl(ip->daddr);
	if (is_initial_rx) {
		// Replace IP address
		ip->daddr = htonl(new_ip);
		// Fix the checksum in IP header
		csum = ~ntohs(ip->check);
		csum -= old_ip;
		csum += new_ip;
		csum = (csum & 0xffff) + (csum >> 16);
		csum = (csum & 0xffff) + (csum >> 16);
		ip->check = ~htons(csum);
	}
#endif


	// Fix the checksum in UDP header
	csum = ~ntohs(udp->check);
//	printf("portIn = %d\n", ntohs(udp->dest));
#if !SIMPLE_SWAP
	if (is_initial_rx) {
		csum -= old_ip;
		csum += new_ip;
	}
#endif
#if 1 // Increment port
	uint16_t old_port = ntohs(udp->dest);
	uint16_t new_port = (old_port + 1) & 0xFFFF;
	csum -= old_port;
	csum += new_port;
	udp->dest = htons(new_port);
#endif
	csum = (csum & 0xffff) + (csum >> 16);
	csum = (csum & 0xffff) + (csum >> 16);
	udp->check = ~htons(csum);
//	printf("portOut= %d\n", ntohs(udp->dest));

	duplicate_and_process_packet(xsk, addr, len);
	/* Here we sent the packet out of the receive port. Note that
		* we allocate one entry and schedule it. Your design would be
		* faster if you do batch processing/transmission */


	bool ret = transmit_packet(xsk, addr, len);
	//complete_tx(xsk);
	return ret;
#if 0 // MSF: Original function:
    /* Lesson#3: Write an IPv6 ICMP ECHO parser to send responses
	 *
	 * Some assumptions to make it easier:
	 * - No VLAN handling
	 * - Only if nexthdr is ICMP
	 * - Just return all data with MAC/IP swapped, and type set to
	 *   ICMPV6_ECHO_REPLY
	 * - Recalculate the icmp checksum */

	if (false) {
		int ret;
		uint32_t tx_idx = 0;
		uint8_t tmp_mac[ETH_ALEN];
		struct in6_addr tmp_ip;
		struct ethhdr *eth = (struct ethhdr *) pkt;
		struct ipv6hdr *ipv6 = (struct ipv6hdr *) (eth + 1);
		struct icmp6hdr *icmp = (struct icmp6hdr *) (ipv6 + 1);

		if (ntohs(eth->h_proto) != ETH_P_IPV6 ||
		    len < (sizeof(*eth) + sizeof(*ipv6) + sizeof(*icmp)) ||
		    ipv6->nexthdr != IPPROTO_ICMPV6 ||
		    icmp->icmp6_type != ICMPV6_ECHO_REQUEST)
			return false;

		memcpy(tmp_mac, eth->h_dest, ETH_ALEN);
		memcpy(eth->h_dest, eth->h_source, ETH_ALEN);
		memcpy(eth->h_source, tmp_mac, ETH_ALEN);

		memcpy(&tmp_ip, &ipv6->saddr, sizeof(tmp_ip));
		memcpy(&ipv6->saddr, &ipv6->daddr, sizeof(tmp_ip));
		memcpy(&ipv6->daddr, &tmp_ip, sizeof(tmp_ip));

		icmp->icmp6_type = ICMPV6_ECHO_REPLY;

		csum_replace2(&icmp->icmp6_cksum,
			      htons(ICMPV6_ECHO_REQUEST << 8),
			      htons(ICMPV6_ECHO_REPLY << 8));

		/* Here we sent the packet out of the receive port. Note that
		 * we allocate one entry and schedule it. Your design would be
		 * faster if you do batch processing/transmission */

		ret = xsk_ring_prod__reserve(&xsk->tx, 1, &tx_idx);
		if (ret != 1) {
			/* No more transmit slots, drop the packet */
			return false;
		}

		xsk_ring_prod__tx_desc(&xsk->tx, tx_idx)->addr = addr;
		xsk_ring_prod__tx_desc(&xsk->tx, tx_idx)->len = len;
		xsk_ring_prod__submit(&xsk->tx, 1);
		xsk->outstanding_tx++;

		xsk->stats.tx_bytes += len;
		xsk->stats.tx_packets++;
		return true;
	}
	return false;
#endif
}

void stuff_fill_ring(struct xsk_socket_info *xsk) {
	unsigned int stock_frames, i;
	uint32_t idx_fq = 0;
	/* Stuff the ring with as much frames as possible */
	stock_frames = xsk_prod_nb_free(&xsk->umem->fq,
					xsk_umem_free_frames(xsk));

	if (stock_frames > 0) {

		stock_frames = xsk_ring_prod__reserve(&xsk->umem->fq, stock_frames,
					     &idx_fq);

		/* This should not happen, but just in case */
//		while (ret != stock_frames)
//			ret = xsk_ring_prod__reserve(&xsk->umem->fq, rcvd,
//						     &idx_fq);

		for (i = 0; i < stock_frames; i++) {
			uint64_t frame = xsk_alloc_umem_frame(xsk);
			if (frame == INVALID_UMEM_FRAME) {
				printf("INVALID FRAME put into fill queue\n");
			}
			*xsk_ring_prod__fill_addr(&xsk->umem->fq, idx_fq++) = frame;
		}

		xsk_ring_prod__submit(&xsk->umem->fq, stock_frames);
	}
}

static unsigned int handle_receive_packets(struct xsk_socket_info *xsk)
{
	unsigned int rcvd, i;
	uint32_t idx_rx = 0;

	rcvd = xsk_ring_cons__peek(&xsk->rx, RX_BATCH_SIZE, &idx_rx);
	if (!rcvd)
		return 0;

	last_batch_size = rcvd;
	if (max_batch_size < rcvd) {
		max_batch_size = rcvd;
	}

	stuff_fill_ring(xsk);

	/* Process received packets */
	for (i = 0; i < rcvd; i++) {
		uint64_t addr = xsk_ring_cons__rx_desc(&xsk->rx, idx_rx)->addr;
		uint32_t len = xsk_ring_cons__rx_desc(&xsk->rx, idx_rx++)->len;

		if (!process_packet(xsk, addr, len, true)) {
			//printf("Releasing packet\n");
			xsk_free_umem_frame(xsk, addr);
		}

		xsk->stats.rx_bytes += len;
	}

	xsk_ring_cons__release(&xsk->rx, rcvd);
	xsk->stats.rx_packets += rcvd;

	//stuff_fill_ring(xsk);

	return rcvd;
  }

static void rx_and_process(struct config *cfg,
			   struct xsk_socket_info *xsk_socket)
{
	struct pollfd fds[2];
	int ret, nfds = 1;

	memset(fds, 0, sizeof(fds));
	fds[0].fd = xsk_socket__fd(xsk_socket->xsk);
	fds[0].events = POLLIN;

	while(!global_exit) {
//		usleep(10);
		//if (cfg->xsk_poll_mode && !xsk_socket->outstanding_tx) { // MSF
		if (cfg->xsk_poll_mode) {
			ret = poll(fds, nfds, -1);
			if (ret <= 0 || ret > 1)
				continue;
		}
#if 1
		while (!global_exit && handle_receive_packets(xsk_socket)) {
			/* Do we need to wake up the kernel for transmission */
			complete_tx(xsk_socket);
		}
	//	complete_tx(xsk_socket);
#else
		handle_receive_packets(xsk_socket)) {
		complete_tx(xsk_socket);
#endif
	}
}

#define NANOSEC_PER_SEC 1000000000 /* 10^9 */
static uint64_t gettime(void)
{
	struct timespec t;
	int res;

	res = clock_gettime(CLOCK_MONOTONIC, &t);
	if (res < 0) {
		fprintf(stderr, "Error with gettimeofday! (%i)\n", res);
		exit(EXIT_FAIL);
	}
	return (uint64_t) t.tv_sec * NANOSEC_PER_SEC + t.tv_nsec;
}

static double calc_period(struct stats_record *r, struct stats_record *p)
{
	double period_ = 0;
	__u64 period = 0;

	period = r->timestamp - p->timestamp;
	if (period > 0)
		period_ = ((double) period / NANOSEC_PER_SEC);

	return period_;
}

static void stats_print(struct stats_record *stats_rec,
			struct stats_record *stats_prev)
{
	uint64_t packets, bytes;
	double period;
	double rx_pps; /* packets per sec */
	double tx_pps; /* packets per sec */
	double bps; /* bits per sec */

	char *fmt = "%-12s %'11lld pkts (%'10.0f pps)"
		" %'11lld Kbytes (%'6.0f Mbits/s)"
		" period:%f\n";

	period = calc_period(stats_rec, stats_prev);
	if (period == 0)
		period = 1;

	packets = stats_rec->rx_packets - stats_prev->rx_packets;
	rx_pps  = packets / period;

	bytes   = stats_rec->rx_bytes   - stats_prev->rx_bytes;
	bps     = (bytes * 8) / period / 1000000;

	printf(fmt, "AF_XDP RX:", stats_rec->rx_packets, rx_pps,
	       stats_rec->rx_bytes / 1000 , bps,
	       period);

	packets = stats_rec->tx_packets - stats_prev->tx_packets;
	tx_pps  = packets / period;

	bytes   = stats_rec->tx_bytes   - stats_prev->tx_bytes;
	bps     = (bytes * 8) / period / 1000000;

	printf(fmt, "       TX:", stats_rec->tx_packets, tx_pps,
	       stats_rec->tx_bytes / 1000 , bps,
	       period);
	printf("  Total completed: %lu, dropped_no_slots=%lu, total_needed=%lu, total_allocs=%lu\n", total_completed, dropped_no_slots, total_needed, total_allocs);
	printf("  lastRxbatchsize: %lu, max_batch_size=%lu, maxcompleted:%lu\n", last_batch_size, max_batch_size, max_completed);
	printf("  rx:tx ratio:  1:%1.4f, recycle_retries=%lu, extra_tx_kick=%lu\n", tx_pps/rx_pps, recycle_retries, extra_tx_kick);
	max_batch_size = 0;
	max_completed = 0;
	printf("\n");
}

static void *stats_poll(void *arg)
{
	unsigned int interval = 2;
	struct xsk_socket_info *xsk = arg;
	static struct stats_record previous_stats = { 0 };

	previous_stats.timestamp = gettime();

	/* Trick to pretty printf with thousands separators use %' */
	setlocale(LC_NUMERIC, "en_US");

	while (!global_exit) {
		sleep(interval);
		xsk->stats.timestamp = gettime();
		stats_print(&xsk->stats, &previous_stats);
		previous_stats = xsk->stats;
	}
	return NULL;
}

static void exit_application(int signal)
{
	int err;

	cfg.unload_all = true;
	err = do_unload(&cfg);
	if (err) {
		fprintf(stderr, "Couldn't detach XDP program on iface '%s' : (%d)\n",
			cfg.ifname, err);
	}

	signal = signal;
	global_exit = true;
}

int main(int argc, char **argv)
{
	int ret;
	void *packet_buffer;
	uint64_t packet_buffer_size;
	DECLARE_LIBBPF_OPTS(bpf_object_open_opts, opts);
	DECLARE_LIBXDP_OPTS(xdp_program_opts, xdp_opts, 0);
	struct rlimit rlim = {RLIM_INFINITY, RLIM_INFINITY};
	struct xsk_umem_info *umem;
	struct xsk_socket_info *xsk_socket;
	pthread_t stats_poll_thread;
	int err;
	char errmsg[1024];

	/* Global shutdown handler */
	signal(SIGINT, exit_application);

	/* Cmdline options can change progname */
	parse_cmdline_args(argc, argv, long_options, &cfg, __doc__);

	/* Required option */
	if (cfg.ifindex == -1) {
		fprintf(stderr, "ERROR: Required option --dev missing\n\n");
		usage(argv[0], __doc__, long_options, (argc == 1));
		return EXIT_FAIL_OPTION;
	}

	/* Load custom program if configured */
	if (cfg.filename[0] != 0) {
		struct bpf_map *map;

		custom_xsk = true;
		xdp_opts.open_filename = cfg.filename;
		xdp_opts.prog_name = cfg.progname;
		xdp_opts.opts = &opts;

		if (cfg.progname[0] != 0) {
			xdp_opts.open_filename = cfg.filename;
			xdp_opts.prog_name = cfg.progname;
			xdp_opts.opts = &opts;

			prog = xdp_program__create(&xdp_opts);
		} else {
			prog = xdp_program__open_file(cfg.filename,
						  NULL, &opts);
		}
		err = libxdp_get_error(prog);
		if (err) {
			libxdp_strerror(err, errmsg, sizeof(errmsg));
			fprintf(stderr, "ERR: loading program: %s\n", errmsg);
			return err;
		}

		err = xdp_program__attach(prog, cfg.ifindex, cfg.attach_mode, 0);
		if (err) {
			libxdp_strerror(err, errmsg, sizeof(errmsg));
			fprintf(stderr, "Couldn't attach XDP program on iface '%s' : %s (%d)\n",
				cfg.ifname, errmsg, err);
			return err;
		}

		/* We also need to load the xsks_map */
		map = bpf_object__find_map_by_name(xdp_program__bpf_obj(prog), "xsks_map");
		xsk_map_fd = bpf_map__fd(map);
		if (xsk_map_fd < 0) {
			fprintf(stderr, "ERROR: no xsks map found: %s\n",
				strerror(xsk_map_fd));
			exit(EXIT_FAILURE);
		}
	}

	/* Allow unlimited locking of memory, so all memory needed for packet
	 * buffers can be locked.
	 */
	if (setrlimit(RLIMIT_MEMLOCK, &rlim)) {
		fprintf(stderr, "ERROR: setrlimit(RLIMIT_MEMLOCK) \"%s\"\n",
			strerror(errno));
		exit(EXIT_FAILURE);
	}

	/* Allocate memory for NUM_FRAMES of the default XDP frame size */
	packet_buffer_size = NUM_FRAMES * FRAME_SIZE;
	if (posix_memalign(&packet_buffer,
			   getpagesize(), /* PAGE_SIZE aligned */
			   packet_buffer_size)) {
		fprintf(stderr, "ERROR: Can't allocate buffer memory \"%s\"\n",
			strerror(errno));
		exit(EXIT_FAILURE);
	}

	/* Initialize shared packet_buffer for umem usage */
	umem = configure_xsk_umem(packet_buffer, packet_buffer_size);
	if (umem == NULL) {
		fprintf(stderr, "ERROR: Can't create umem \"%s\"\n",
			strerror(errno));
		exit(EXIT_FAILURE);
	}

	/* Open and configure the AF_XDP (xsk) socket */
	xsk_socket = xsk_configure_socket(&cfg, umem);
	if (xsk_socket == NULL) {
		fprintf(stderr, "ERROR: Can't setup AF_XDP socket \"%s\"\n",
			strerror(errno));
		exit(EXIT_FAILURE);
	}

	/* Start thread to do statistics display */
	if (verbose) {
		ret = pthread_create(&stats_poll_thread, NULL, stats_poll,
				     xsk_socket);
		if (ret) {
			fprintf(stderr, "ERROR: Failed creating statistics thread "
				"\"%s\"\n", strerror(errno));
			exit(EXIT_FAILURE);
		}
	}

	/* Receive and count packets than drop them */
	rx_and_process(&cfg, xsk_socket);

	/* Cleanup */
	xsk_socket__delete(xsk_socket->xsk);
	xsk_umem__delete(umem->umem);

	return EXIT_OK;
}
