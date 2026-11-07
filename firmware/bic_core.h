/* Bisect-Index-Choose (BIC) solver in portable C, a port of run_BIC in
 * bic/bic.py for f_i(x) = A_i * log(B_i * x + C_i) with per-EV maximum rates
 * xmax_i. EVs with equal xmax_i form a rating group. Used by the Raspberry Pi
 * Pico firmware (main_wifi.c via bic_service.c) and, compiled as a
 * shared library, by scripts/pico_run_pc.py.
 *
 * No dynamic allocation: the caller provides every buffer, so the same code
 * runs on a microcontroller with static arrays.
 */
#ifndef BIC_CORE_H
#define BIC_CORE_H

#include <stdint.h>

#if defined(BIC_SHARED) && defined(_WIN32)
#define BIC_API __declspec(dllexport)
#else
#define BIC_API
#endif

/* Budget-residual stopping rule shared by every bisection (DELTA_REL in
 * bic/bic.py): accept 0 <= budget - S(lambda) <= BIC_DELTA_REL * budget. */
#define BIC_DELTA_REL 1e-6

/* Largest number of distinct maximum rates (rating groups). */
#define BIC_MAX_GROUPS 8

/* Which branch of run_BIC produced the allocation. */
#define BIC_PATH_ALL_MAX 0  /* nonbinding budget, every EV at its xmax */
#define BIC_PATH_FAST    1  /* Everett fast path */
#define BIC_PATH_CHOOSE  2  /* indexing and choosing phases */

/* Return codes. */
#define BIC_OK            0
#define BIC_ERR_INPUT    -2  /* an input violates the assumptions of run_BIC */
#define BIC_ERR_RESULT   -3  /* allocation failed the final feasibility check */
#define BIC_ERR_GROUPS   -4  /* more than BIC_MAX_GROUPS distinct ratings */

typedef struct {
    int32_t path;      /* BIC_PATH_* */
    int32_t c_best;    /* number of EVs switched on */
    int32_t chain_ok;  /* 1 if every group's priority order was verified */
    int32_t n_groups;  /* number of rating groups (choosing path) */
    double  lam;       /* multiplier that defines the allocation (0: all at max) */
    double  objval;    /* sum_i A_i * log(B_i * x_i + C_i) */
} bic_result_t;

/* Doubles of workspace per EV. */
#define BIC_WORK_PER_EV 7

/* Solve one period. Inputs A, B, C, xmax have length n (at most 32767); x
 * receives the allocation. Workspace: work holds BIC_WORK_PER_EV * n
 * doubles and order n int32 values. They are overwritten.
 *
 * fastpath = 1 first tries the Everett fast path. Otherwise, or when the
 * budget lies in an Everett gap, the indexing and choosing phases of
 * bic/bic.py run: each rating group is sorted in the priority order, and
 * the search over the counts of switched-on EVs per group (_choosing_phase)
 * solves each on-set restriction by bisection. */
BIC_API int bic_solve(double budget, double eps,
                      const double *A, const double *B, const double *C,
                      const double *xmax, int32_t n, double xmin,
                      int32_t fastpath,
                      double *x, double *work, int32_t *order, bic_result_t *res);

#endif
