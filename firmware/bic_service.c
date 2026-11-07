/* See bic_service.h. Compiled for the Pico, or with BIC_HOST_TEST for the
 * PC (host/bench_host.c). */
#include <string.h>

#include "bic_service.h"

#ifdef BIC_HOST_TEST
#include <time.h>
static uint64_t now_us(void) { return (uint64_t)clock() * 1000000u / CLOCKS_PER_SEC; }
static uint32_t sys_hz(void) { return 0; }
#else
#include "hardware/clocks.h"
#include "pico/stdlib.h"
static uint64_t now_us(void) { return time_us_64(); }
static uint32_t sys_hz(void) { return clock_get_hz(clk_sys); }
#endif

#ifndef BIC_MAX_N
#define BIC_MAX_N 2000
#endif

static double A[BIC_MAX_N], B[BIC_MAX_N], C[BIC_MAX_N], X[BIC_MAX_N];
static double XMAX[BIC_MAX_N];
static double WORK[BIC_WORK_PER_EV * BIC_MAX_N];
static double T_REM[BIC_MAX_N], E_REM[BIC_MAX_N];
static int32_t ORDER[BIC_MAX_N];

int svc_kind(const uint8_t magic[4])
{
    if (memcmp(magic, "BICQ", 4) == 0)
        return SVC_SOLVE;
    if (memcmp(magic, "EVSQ", 4) == 0)
        return SVC_EV_STATE;
    if (memcmp(magic, "BICM", 4) == 0)
        return SVC_SOLVE_MIXED;
    if (memcmp(magic, "EVSM", 4) == 0)
        return SVC_EV_STATE_MIXED;
    return SVC_NONE;
}

uint32_t svc_bytes_per_ev(int kind)
{
    switch (kind) {
    case SVC_SOLVE:          return 24u;
    case SVC_EV_STATE:       return 16u;
    case SVC_SOLVE_MIXED:    return 32u;
    case SVC_EV_STATE_MIXED: return 24u;
    default:                 return 0u;
    }
}

uint8_t *svc_payload_dest(int kind, uint32_t n, uint64_t offset, size_t *room)
{
    if (n > BIC_MAX_N || n == 0) {
        *room = (size_t)-1;
        return NULL;
    }
    const uint64_t block = 8ull * n;
    uint64_t which = offset / block, within = offset % block;
    double *arr;
    if (kind == SVC_SOLVE || kind == SVC_SOLVE_MIXED)
        arr = which == 0 ? A : which == 1 ? B : which == 2 ? C : XMAX;
    else
        arr = which == 0 ? T_REM : which == 1 ? E_REM : XMAX;
    *room = (size_t)(block - within);
    return (uint8_t *)arr + within;
}

/* sLLF utilities from the EV states, as in bic/simulator.py. */
static void form_utilities(uint32_t n)
{
    for (uint32_t i = 0; i < n; i++) {
        double c = T_REM[i] - 60.0 * E_REM[i] / XMAX[i] - 1.0;
        A[i] = XMAX[i];
        B[i] = 1.0 / XMAX[i];
        C[i] = c > 1e-6 ? c : 1e-6;
    }
}

static void put_u32(uint8_t *p, uint32_t v) { memcpy(p, &v, 4); }
static void put_u64(uint8_t *p, uint64_t v) { memcpy(p, &v, 8); }
static void put_f64(uint8_t *p, double v) { memcpy(p, &v, 8); }

uint32_t svc_execute(int kind, const uint8_t hdr[SVC_REQ_HEADER],
                     uint8_t rep[SVC_REP_HEADER], const double **x)
{
    uint32_t n, reps, flags;
    double budget, eps, xmin, xmax;
    memcpy(&n, hdr + 4, 4);
    memcpy(&reps, hdr + 8, 4);
    memcpy(&flags, hdr + 12, 4);
    memcpy(&budget, hdr + 16, 8);
    memcpy(&eps, hdr + 24, 8);
    memcpy(&xmin, hdr + 32, 8);
    memcpy(&xmax, hdr + 40, 8);
    if (reps == 0)
        reps = 1;

    int32_t status = BIC_OK;
    bic_result_t res = {0};
    uint64_t t_min = 0, t_total = 0;
    int ev_state = (kind == SVC_EV_STATE || kind == SVC_EV_STATE_MIXED);
    int mixed = (kind == SVC_SOLVE_MIXED || kind == SVC_EV_STATE_MIXED);

    if (n > BIC_MAX_N) {
        status = -1;
    } else if (n > 0) {
        if (!mixed)
            for (uint32_t i = 0; i < n; i++)
                XMAX[i] = xmax;
        t_min = UINT64_MAX;
        for (uint32_t r = 0; r < reps && status == BIC_OK; r++) {
            uint64_t t0 = now_us();
            if (ev_state)
                form_utilities(n);
            status = bic_solve(budget, eps, A, B, C, XMAX, (int32_t)n, xmin,
                               (flags >> 1) & 1u, X, WORK, ORDER, &res);
            uint64_t dt = now_us() - t0;
            t_total += dt;
            if (dt < t_min)
                t_min = dt;
        }
    }

    uint32_t n_out = (status == BIC_OK) ? n : 0;
    memcpy(rep, "BICR", 4);
    put_u32(rep + 4, (uint32_t)status);
    put_u32(rep + 8, n_out);
    put_u32(rep + 12, (uint32_t)res.path);
    put_u32(rep + 16, (uint32_t)res.c_best);
    put_u32(rep + 20, ((uint32_t)res.chain_ok & 0xFFFFu)
                      | ((uint32_t)res.n_groups << 16));
    put_u32(rep + 24, sys_hz());
    put_u32(rep + 28, reps);
    put_u64(rep + 32, t_min);
    put_u64(rep + 40, t_total);
    put_f64(rep + 48, res.objval);
    *x = X;
    return n_out;
}
