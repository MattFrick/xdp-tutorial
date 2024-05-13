/* SPDX-License-Identifier: GPL-2.0 */

#include <linux/bpf.h>
#include <arpa/inet.h>
#include <bpf/bpf_helpers.h>
#include <xdp/parsing_helpers.h>

struct {
	__uint(type, BPF_MAP_TYPE_XSKMAP);
	__type(key, __u32);
	__type(value, __u32);
	__uint(max_entries, 64);
} xsks_map SEC(".maps");

struct {
	__uint(type, BPF_MAP_TYPE_PERCPU_ARRAY);
	__type(key, __u32);
	__type(value, __u32);
	__uint(max_entries, 64);
} xdp_stats_map SEC(".maps");

SEC("xdp")
int xdp_sock_prog(struct xdp_md *ctx)
{
	void *data_end = (void *)(long)ctx->data_end;
	void *data = (void *)(long)ctx->data;
    int index = ctx->rx_queue_index;
	struct hdr_cursor nh = { .pos = data };
	int eth_type, ip_type;
	struct ethhdr *eth;
	struct iphdr *iphdr;
	struct ipv6hdr *ipv6hdr;
    struct udphdr *udphdr;

	if (data + sizeof(*eth) > data_end) {
		goto out;
    }

	eth_type = parse_ethhdr(&nh, data_end, &eth);
    if (eth_type < 0) {
		goto out;
    }

	if (eth_type == bpf_htons(ETH_P_IP)) {
		ip_type = parse_iphdr(&nh, data_end, &iphdr);
	} else if (eth_type == bpf_htons(ETH_P_IPV6)) {
		ip_type = parse_ip6hdr(&nh, data_end, &ipv6hdr);
	} else {
		goto out;
	}

	if (ip_type == IPPROTO_UDP) {
#define UPPER_PORT 8020
#define LOWER_PORT 8007

		if (parse_udphdr(&nh, data_end, &udphdr) < 0) {
			goto out;
		}
		if (ntohs(udphdr->dest) >= LOWER_PORT &&
            ntohs(udphdr->dest) <= UPPER_PORT)
        {
			/* A set entry here means that the correspnding queue_id
			* has an active AF_XDP socket bound to it. */
			if (bpf_map_lookup_elem(&xsks_map, &index)) {
				return bpf_redirect_map(&xsks_map, index, 0);
			}
        }
	}

out:
    return XDP_PASS;
#if 0 // MSF: Original AF_XDP code:
    int index = ctx->rx_queue_index;
    __u32 *pkt_count;

    pkt_count = bpf_map_lookup_elem(&xdp_stats_map, &index);
    if (pkt_count) {

        /* We pass every other packet */
        if ((*pkt_count)++ & 1)
            return XDP_PASS;
    }



    return XDP_PASS;
#endif
}

char _license[] SEC("license") = "GPL";
