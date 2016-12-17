#include <linux/kernel.h>
#include <linux/random.h>
#include <linux/module.h>
#include <net/tcp.h>


#define HYSTART_ACK_TRAIN	1
#define HYSTART_DELAY		2
#define TCP_EASTWOOD_RTT_MIN   (HZ/20)	/* 50ms */
#define TCP_EASTWOOD_INIT_RTT  (20*HZ)	/* maybe too conservative?! */

static int window __read_mostly = 8;
static unsigned int backoff_beta __read_mostly = 0.7071 * 1024; /* sqrt 0.5 */
static unsigned int backoff_factor __read_mostly = 42;
static unsigned int hystart_detect __read_mostly = 3;
static unsigned int use_ineff __read_mostly = 5;
static unsigned int use_shadow __read_mostly = 1;
static unsigned int backoff __read_mostly = 0;
static unsigned int use_tolerance __read_mostly = 1;
static unsigned int shadow_fast __read_mostly = 1;
static unsigned int shadow_grow __read_mostly = 1;
static unsigned int recovery_restore __read_mostly = 0;
static unsigned int loss_push __read_mostly = 1;
static unsigned int use_sack __read_mostly = 1;

module_param(window, int, 0444);
MODULE_PARM_DESC(window, "gradient window size (power of two <= 256)");
module_param(backoff_beta, uint, 0644);
MODULE_PARM_DESC(backoff_beta, "backoff beta (0-1024)");
module_param(backoff_factor, uint, 0644);
MODULE_PARM_DESC(backoff_factor, "backoff probability scale factor");
module_param(hystart_detect, uint, 0644);
MODULE_PARM_DESC(hystart_detect, "use Hybrid Slow start "
		 "(0: disabled, 1: ACK train, 2: delay threshold, 3: both)");
module_param(use_ineff, uint, 0644);
MODULE_PARM_DESC(use_ineff, "use ineffectual backoff detection (threshold)");
module_param(use_shadow, uint, 0644);
MODULE_PARM_DESC(use_shadow, "use shadow window heuristic");
module_param(backoff, uint, 0644);
MODULE_PARM_DESC(backoff, "back");
module_param(use_tolerance, uint, 0644);
MODULE_PARM_DESC(use_tolerance, "use loss tolerance heuristic");
module_param(shadow_fast, uint, 0644);
MODULE_PARM_DESC(shadow_fast, "back");
module_param(shadow_grow, uint, 0644);
MODULE_PARM_DESC(shadow_grow, "back");
module_param(recovery_restore, uint, 0644);
MODULE_PARM_DESC(recovery_restore, "back");
module_param(loss_push, uint, 0644);
MODULE_PARM_DESC(loss_push, "back");
module_param(use_sack, uint, 0644);
MODULE_PARM_DESC(use_sack, "back");

struct bugs_minmax {
    union {
	struct {
	    s32 min;
	    s32 max;
	};
	u64 v64;
    };
};

enum bugs_state {
    BU_GS_UNKNOWN = 0,
    BU_GS_NONFULL = 1,
    BU_GS_FULL    = 2,
    BU_GS_BACKOFF = 3,
};

struct bugs {
    struct bugs_minmax rtt;
    struct bugs_minmax rtt_prev;
    struct bugs_minmax *gradients;
    struct bugs_minmax gsum;
    bool gfilled;
    u8  tail;
    u8  state;
    u8  delack;
    u8     first_ack;        /* flag which infers that this is the first ack */
    u8     reset_rtt_min;    /* Reset RTT min to next RTT sample*/
    u32 rtt_seq;
    u32 undo_cwnd;
    u32 shadow_wnd;
    u32 snd_cwnd_cnt;
    u16 backoff_cnt;
    u16 sample_cnt;
    s32 delay_min;
    s32 ack_sack_cnt;
    u32 last_ack;
    u32 round_start;

    u32    bw_ns_est;        /* first bandwidth estimation..not too smoothed 8) */
    u32    bw_est;           /* bandwidth estimate */
    u32    rtt_win_sx;       /* here starts a new evaluation... */
    u32    bk;
    u32    snd_una;          /* used for evaluating the number of acked bytes */
    u32    cumul_ack;
    u32    accounted;
    u32    east_rtt;
    u32    rtt_min;          /* minimum observed RTT */
};

/**
 * nexp_u32 - negative base-e exponential
 * @ux: x in units of micro
 *
 * Returns exp(ux * -1e-6) * U32_MAX.
 */
static u32 __pure nexp_u32(u32 ux)
{
    static const u16 v[] = {
	/* exp(-x)*65536-1 for x = 0, 0.000256, 0.000512, ... */
	65535,
	65518, 65501, 65468, 65401, 65267, 65001, 64470, 63422,
	61378, 57484, 50423, 38795, 22965, 8047,  987,   14,
    };
    u32 msb = ux >> 8;
    u32 res;
    int i;
    /* Cut off when ux >= 2^24 (actual result is <= 222/U32_MAX). */
    if (msb > U16_MAX)
	return 0;

    /* Scale first eight bits linearly: */
    res = U32_MAX - (ux & 0xff) * (U32_MAX / 1000000);

    /* Obtain e^(x + y + ...) by computing e^x * e^y * ...: */
    for (i = 1; msb; i++, msb >>= 1) {
	u32 y = v[i & -(msb & 1)] + U32_C(1);

	res = ((u64)res * y) >> 16;
    }

    return res;
}

/* Based on the HyStart algorithm (by Ha et al.) that is implemented in
 * tcp_cubic. Differences/experimental changes:
 *   o Using Hayes' delayed ACK filter.
 *   o Using a usec clock for the ACK train.
 *   o Reset ACK train when application limited.
 *   o Invoked at any cwnd (i.e. also when cwnd < 16).
 *   o Invoked only when cwnd < ssthresh (i.e. not when cwnd == ssthresh).
 */
static void tcp_bugs_hystart_update(struct sock *sk)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);

    ca->delay_min = min_not_zero(ca->delay_min, ca->rtt.min);
    if (ca->delay_min == 0)
	return;

    if (hystart_detect & HYSTART_ACK_TRAIN) {
	u32 now_us = div_u64(local_clock(), NSEC_PER_USEC);

	if (ca->last_ack == 0 || !tcp_is_cwnd_limited(sk, tcp_packets_in_flight(tp))) {
	    ca->last_ack = now_us;
	    ca->round_start = now_us;
	} else if (before(now_us, ca->last_ack + 3000)) {
	    u32 base_owd = max(ca->delay_min / 2U, 125U);

	    ca->last_ack = now_us;
	    if (after(now_us, ca->round_start + base_owd)) {
		tp->snd_ssthresh = tp->snd_cwnd;
		return;
	    }
	}
    }

    if (hystart_detect & HYSTART_DELAY) {
	if (ca->sample_cnt < 8) {
	    ca->sample_cnt++;
	} else {
	    s32 thresh = max(ca->delay_min + ca->delay_min / 8U, 125U);

	    if (ca->rtt.min > thresh) {
		tp->snd_ssthresh = tp->snd_cwnd;
	    }
	}
    }
}

static s32 tcp_bugs_grad(struct bugs *ca)
{
    s32 gmin = ca->rtt.min - ca->rtt_prev.min;
    s32 gmax = ca->rtt.max - ca->rtt_prev.max;
    s32 grad;

    if (ca->gradients) {
	ca->gsum.min += gmin - ca->gradients[ca->tail].min;
	ca->gsum.max += gmax - ca->gradients[ca->tail].max;
	ca->gradients[ca->tail].min = gmin;
	ca->gradients[ca->tail].max = gmax;
	ca->tail = (ca->tail + 1) & (window - 1);
	gmin = ca->gsum.min;
	gmax = ca->gsum.max;
    }

    /* We keep sums to ignore gradients during cwnd reductions;
     * the paper's smoothed gradients otherwise simplify to:
     * (rtt_latest - rtt_oldest) / window.
     *
     * We also drop division by window here.
     */
    grad = gmin > 0 ? gmin : gmax;

    /* Extrapolate missing values in gradient window: */
    if (!ca->gfilled) {
	if (!ca->gradients && window > 1)
	    grad *= window; /* Memory allocation failed. */
	else if (ca->tail == 0)
	    ca->gfilled = true;
	else
	    grad = (grad * window) / (int)ca->tail;
    }

    /* Backoff was effectual: */
    if (gmin <= -32 || gmax <= -32)
	ca->backoff_cnt = 0;

    if (use_tolerance) {
	/* Reduce small variations to zero: */
	gmin = DIV_ROUND_CLOSEST(gmin, 64);
	gmax = DIV_ROUND_CLOSEST(gmax, 64);
	if (gmin > 0 && gmax <= 0)
	    ca->state = BU_GS_FULL;
	else if ((gmin > 0 && gmax > 0) || gmax < 0)
	    ca->state = BU_GS_NONFULL;
    }
    return grad;
}

void tcp_enter_cwr_1(struct sock *sk)
{
    struct tcp_sock *tp = tcp_sk(sk);

    tp->prior_ssthresh = 0;
    if (inet_csk(sk)->icsk_ca_state < TCP_CA_CWR) {
	tp->undo_marker = 0;
	tp->high_seq = tp->snd_nxt;
	tp->tlp_high_seq = 0;
	tp->snd_cwnd_cnt = 0;
	tp->prior_cwnd = tp->snd_cwnd;
	tp->prr_delivered = 0;
	tp->prr_out = 0;
	tp->snd_ssthresh = inet_csk(sk)->icsk_ca_ops->ssthresh(sk);
	if (tp->ecn_flags & TCP_ECN_OK)
	    tp->ecn_flags |= TCP_ECN_QUEUE_CWR;
	tcp_set_ca_state(sk, TCP_CA_CWR);
    }
}

static bool tcp_bugs_backoff(struct sock *sk, u32 grad)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);

    if (prandom_u32() <= nexp_u32(grad * backoff_factor))
	return false;

    if (use_ineff) {
	ca->backoff_cnt++;
	if (ca->backoff_cnt > use_ineff)
	    return false;
    }

    ca->shadow_wnd = max(ca->shadow_wnd, tp->snd_cwnd);
    ca->state = BU_GS_BACKOFF;
    tcp_enter_cwr_1(sk);
    return true;
}

void tcp_cong_avoid_ai_shadow(struct sock *sk, u32 w, u32 acked)
{
    struct tcp_sock *tp = tcp_sk(sk);
    struct bugs *ca = inet_csk_ca(sk);
    if (ca->snd_cwnd_cnt >= w) {
	ca->snd_cwnd_cnt = 0;
	ca->shadow_wnd ++;
    }

    ca->snd_cwnd_cnt += acked;
    if (ca->snd_cwnd_cnt >= w) {
	u32 delta = ca->snd_cwnd_cnt / w;

	ca->snd_cwnd_cnt -= delta * w;
	ca->shadow_wnd += delta;
    }
    ca->shadow_wnd = min(ca->shadow_wnd, tp->snd_cwnd_clamp);
}

/* Not called in CWR or Recovery state. */
static void tcp_bugs_cong_avoid(struct sock *sk, u32 ack, u32 acked)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);
    u32 prior_snd_cwnd;
    u32 incr;

    if (tp->snd_cwnd <= tp->snd_ssthresh && hystart_detect)
	tcp_bugs_hystart_update(sk);

    if (after(ack, ca->rtt_seq) && ca->rtt.v64) {
	s32 grad = 0;

	if (ca->rtt_prev.v64)
	    grad = tcp_bugs_grad(ca);
	ca->rtt_seq = tp->snd_nxt;
	ca->rtt_prev = ca->rtt;
	ca->rtt.v64 = 0;
	ca->last_ack = 0;
	ca->sample_cnt = 0;

	if (backoff && grad > 0 && tcp_bugs_backoff(sk, grad))
	    return;
    }

    if (!tcp_is_cwnd_limited(sk, tcp_packets_in_flight(tp))) {
	ca->shadow_wnd = min(ca->shadow_wnd, tp->snd_cwnd);
	return;
    }

    prior_snd_cwnd = tp->snd_cwnd;
    tcp_reno_cong_avoid(sk, ack, acked);

    incr = tp->snd_cwnd - prior_snd_cwnd;
    ca->shadow_wnd = max(ca->shadow_wnd, ca->shadow_wnd + incr);
}

static void tcp_bugs_acked(struct sock *sk, u32 num_acked, s32 rtt_us)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);

    if (rtt_us <= 0)
	return;

    /* A heuristic for filtering delayed ACKs, adapted from:
     * D.A. Hayes. "Timing enhancements to the FreeBSD kernel to support
     * delay and rate based TCP mechanisms." TR 100219A. CAIA, 2010.
     */
    if (tp->sacked_out == 0) {
	if (num_acked == 1 && ca->delack) {
	/* A delayed ACK is only used for the minimum if it is
	 * provenly lower than an existing non-zero minimum.
	 */
	ca->rtt.min = min(ca->rtt.min, rtt_us);
	ca->delack--;
	return;
	} else if (num_acked > 1 && ca->delack < 5) {
	    ca->delack++;
	}
    }

    ca->rtt.min = min_not_zero(ca->rtt.min, rtt_us);
    ca->rtt.max = max(ca->rtt.max, rtt_us);

    if (rtt_us > 0)
	ca->east_rtt = usecs_to_jiffies(rtt_us);
}

static u32 tcp_bugs_ssthresh(struct sock *sk)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);

    ca->undo_cwnd = tp->snd_cwnd;
    ca->snd_cwnd_cnt = 0;
    ca->ack_sack_cnt = tcp_packets_in_flight(tp);

    if (ca->state == BU_GS_BACKOFF)
	return max(2U, (tp->snd_cwnd * min(1024U, backoff_beta)) >> 10);

    if (ca->state == BU_GS_NONFULL && use_tolerance)
	return tp->snd_cwnd;

    ca->shadow_wnd = max(min(ca->shadow_wnd >> 1, tp->snd_cwnd), 2U);
    if (use_shadow)
	return max3(2U, ca->shadow_wnd, tp->snd_cwnd >> 1);
    return max(2U, tp->snd_cwnd >> 1);
}

static u32 tcp_bugs_undo_cwnd(struct sock *sk)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);
    return max3(2U, ca->shadow_wnd, max(tp->snd_cwnd, ca->undo_cwnd));
}

static void tcp_bugs_init(struct sock *sk)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);

    if (window > 1)
	ca->gradients = kcalloc(window, sizeof(ca->gradients[0]),
					GFP_NOWAIT | __GFP_NOWARN);
    ca->rtt_seq = tp->snd_nxt;
    ca->shadow_wnd = tp->snd_cwnd;
    ca->ack_sack_cnt = 0;
    // eastwood
    ca->bk = 0;
    ca->bw_ns_est = 0;
    ca->bw_est = 0;
    ca->accounted = 0;
    ca->cumul_ack = 0;
    ca->reset_rtt_min = 1;
    ca->rtt_min = ca->east_rtt = TCP_EASTWOOD_INIT_RTT;
    ca->rtt_win_sx = tcp_time_stamp;
    ca->snd_una = tcp_sk(sk)->snd_una;
    ca->first_ack = 1;
}

static void tcp_bugs_release(struct sock *sk)
{
    struct bugs *ca = inet_csk_ca(sk);

    kfree(ca->gradients);
}

static inline u32 eastwood_do_filter(u32 a, u32 b)
{
    return ((7 * a) + b) >> 3;
}

static void eastwood_filter(struct bugs *ca, u32 delta)
{
    if (ca->bw_ns_est == 0 && ca->bw_est == 0) {
	ca->bw_ns_est = ca->bk / delta;
	ca->bw_est = ca->bw_ns_est;
    } else {
	ca->bw_ns_est = eastwood_do_filter(ca->bw_ns_est, ca->bk / delta);
	ca->bw_est = eastwood_do_filter(ca->bw_est, ca->bw_ns_est);
    }
}

static void eastwood_update_window(struct sock *sk)
{
    struct bugs *ca = inet_csk_ca(sk);
    s32 delta = tcp_time_stamp - ca->rtt_win_sx;

    if (ca->first_ack) {
	ca->snd_una = tcp_sk(sk)->snd_una;
	ca->first_ack = 0;
    }

    if (ca->east_rtt && delta > max_t(u32, ca->east_rtt, TCP_EASTWOOD_RTT_MIN)) {
	eastwood_filter(ca, delta);
	ca->bk = 0;
	ca->rtt_win_sx = tcp_time_stamp;
    }
}

static inline void update_rtt_min(struct bugs *ca)
{
    if (ca->reset_rtt_min) {
	ca->rtt_min = ca->east_rtt;
	ca->reset_rtt_min = 0;
    } else
	ca->rtt_min = min(ca->east_rtt, ca->rtt_min);
}

static inline void eastwood_fast_bw(struct sock *sk)
{
    const struct tcp_sock *tp = tcp_sk(sk);
    struct bugs *ca = inet_csk_ca(sk);
    
    eastwood_update_window(sk);

    ca->bk += tp->snd_una - ca->snd_una;
    ca->snd_una = tp->snd_una;
    update_rtt_min(ca);
}

static inline u32 eastwood_acked_count(struct sock *sk)
{
    const struct tcp_sock *tp = tcp_sk(sk);
    struct bugs *ca = inet_csk_ca(sk);

    ca->cumul_ack = tp->snd_una - ca->snd_una;

    if (!ca->cumul_ack) {
	ca->accounted += tp->mss_cache;
	ca->cumul_ack = tp->mss_cache;
    }

    if (ca->cumul_ack > tp->mss_cache) {
	/* Partial or delayed ack */
	if (ca->accounted >= ca->cumul_ack) {
	    ca->accounted -= ca->cumul_ack;
	    ca->cumul_ack = tp->mss_cache;
	} else {
	    ca->cumul_ack -= ca->accounted;
	    ca->accounted = 0;
	}
    }
    ca->snd_una = tp->snd_una;
    return ca->cumul_ack;
}

static u32 tcp_eastwood_bw_rttmin(const struct sock *sk)
{
    const struct tcp_sock *tp = tcp_sk(sk);
    const struct bugs *ca = inet_csk_ca(sk);
    return max_t(u32, (ca->bw_est * ca->rtt_min) / tp->mss_cache, 2);
}

static int bugs_main(struct sock *sk, struct rate_sample *rs)
{
    struct inet_connection_sock *icsk = inet_csk(sk);
    struct tcp_sock *tp = tcp_sk(sk);
    struct bugs *ca = inet_csk_ca(sk);
	
    if (!shadow_grow) {
	goto eastwood;
    }
		
    if (icsk->icsk_ca_state != TCP_CA_Open) {
	if (rs->rtt_us) {
	    ca->rtt.min = min_not_zero(ca->rtt.min, (s32)rs->rtt_us);
	    ca->rtt.max = max(ca->rtt.max, (s32)rs->rtt_us);
	}
		
	if (ca->state == BU_GS_NONFULL && use_tolerance) {	
	    if (!shadow_fast && (ca->ack_sack_cnt < 0 || ca->ack_sack_cnt == 0) && ca->rtt.v64) {
		s32 grad = 0;

		if (ca->rtt_prev.v64)
		    grad = tcp_bugs_grad(ca);
		ca->rtt_prev = ca->rtt;
		ca->ack_sack_cnt = tcp_packets_in_flight(tp);
		ca->rtt.v64 = 0;
	    }
	    ca->ack_sack_cnt -= rs->acked_sacked;
	    if (ca->state == BU_GS_NONFULL || shadow_fast) {
		tcp_cong_avoid_ai_shadow(sk, ca->shadow_wnd, rs->acked_sacked);	
		tp->snd_cwnd = ca->shadow_wnd;
	    }
	}
    } 

eastwood:
    if (use_sack) {
	eastwood_update_window(sk);	
	ca->bk += rs->acked_sacked * tp->mss_cache;
	update_rtt_min(ca);
    }
    return CONG_CONT;
}

static void bugs_state(struct sock *sk, u8 new_state)
{
    struct inet_connection_sock *icsk = inet_csk(sk);
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);

    if (!recovery_restore) {
	return;
    }

    if (icsk->icsk_ca_state && new_state == TCP_CA_Open) {
	ca->rtt_seq = tp->snd_nxt;
	ca->rtt_prev = ca->rtt;
	ca->rtt.v64 = 0;
	ca->state = BU_GS_UNKNOWN;
    }
    if (new_state == TCP_CA_Open && ca->state == BU_GS_NONFULL) {
	tp->snd_cwnd = max(max(tp->snd_cwnd, ca->shadow_wnd), 2U);
    }
    if (new_state == TCP_CA_Loss) {
	if (ca->state == BU_GS_NONFULL && use_tolerance) {
	    tp->snd_cwnd = ca->shadow_wnd;
	    if (loss_push)
		tcp_push_pending_frames(sk);
	} 
    }
}

static void tcp_bugs_cwnd_event(struct sock *sk, const enum tcp_ca_event ev)
{
    struct bugs *ca = inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);
    struct bugs_minmax *gradients;

    switch (ev) {
	case CA_EVENT_FAST_ACK:
	    if (!use_sack)
		eastwood_fast_bw(sk);
	    break;
	case CA_EVENT_SLOW_ACK:
	    if (!use_sack) {
		eastwood_update_window(sk);
		ca->bk += eastwood_acked_count(sk);
		update_rtt_min(ca);
	    }
	    break;
	case CA_EVENT_CWND_RESTART:
	    gradients = ca->gradients;
	    if (gradients)
		memset(gradients, 0, window * sizeof(gradients[0]));
	    memset(ca, 0, sizeof(*ca));

	    ca->gradients = gradients;
	    ca->rtt_seq = tp->snd_nxt;
	    ca->shadow_wnd = tp->snd_cwnd;
	    break;
	case CA_EVENT_COMPLETE_CWR:
	    tp->snd_cwnd = tp->snd_ssthresh = tcp_eastwood_bw_rttmin(sk);
	    break;
	case CA_EVENT_LOSS:
	    tp->snd_ssthresh = tcp_eastwood_bw_rttmin(sk);
	    ca->reset_rtt_min = 1;
	    break;
	default:
	    break;
    }
}


struct tcp_congestion_ops tcp_bugs __read_mostly = {
    .cong_avoid = tcp_bugs_cong_avoid,
    .cong_collect	= bugs_main,
    .set_state = bugs_state,
    .cwnd_event = tcp_bugs_cwnd_event,
    .pkts_acked = tcp_bugs_acked,
    .undo_cwnd = tcp_bugs_undo_cwnd,
    .ssthresh = tcp_bugs_ssthresh,
    .release = tcp_bugs_release,
    .init = tcp_bugs_init,
    .owner = THIS_MODULE,
    .name = "bugs",
};

static int __init tcp_bugs_register(void)
{
    if (backoff_beta > 1024 || window < 1 || window > 256)
	return -ERANGE;
    if (!is_power_of_2(window))
	return -EINVAL;

    BUILD_BUG_ON(sizeof(struct bugs) > ICSK_CA_PRIV_SIZE);
    tcp_register_congestion_control(&tcp_bugs);
    return 0;
}

static void __exit tcp_bugs_unregister(void)
{
    tcp_unregister_congestion_control(&tcp_bugs);
}

module_init(tcp_bugs_register);
module_exit(tcp_bugs_unregister);
MODULE_AUTHOR("fix");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("TCP BU_GS");
