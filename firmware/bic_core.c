/* Port of run_BIC (bic/bic.py). The bisections take the midpoints and
 * decisions of the Python code; only the way S(lambda) and the values of the
 * restrictions are evaluated differs, so the two implementations agree to
 * rounding.
 *
 * Sorted evaluation. In the priority order of a rating group, the
 * multipliers f'(xmax) and f'(xmin), at which an EV leaves its maximum rate
 * and reaches xmin, do not increase, and neither does lambda_th. At any
 * lambda the EVs of a group prefix therefore form three runs: at xmax,
 * interior (x = A/lambda - C/B), at xmin. Two binary searches and prefix
 * sums give S(lambda) and the value of a restriction in O(K log n) instead
 * of O(n). The thresholds are checked to be non-increasing; otherwise the
 * per-EV loops of the Python code run.
 *
 * Stored bisection path. The choosing phase solves many restrictions whose
 * on-sets differ by a few EVs, and each bisection starts from the same
 * bracket [0, L]. The steps of the bisections are kept: at each depth the
 * midpoint, S for the on-set that computed it, the run boundaries over the
 * whole group, and the decision taken. A restriction follows the stored
 * steps while its own decision is the stored one. It decides from the
 * stored S and the EVs that differ, each of which contributes between xmin
 * and its xmax, and corrects the stored S by these EVs when that bound does
 * not decide. Once no threshold of the on-set lies inside the bracket,
 * S = alpha/lambda + beta, and the remaining steps compare the midpoint with
 * the multipliers at which S = budget and S = budget - tol. */
#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "bic_core.h"

/* np.minimum(hi, np.maximum(lo, v)) */
static double clip(double v, double lo, double hi)
{
    if (v < lo) v = lo;
    if (v > hi) v = hi;
    return v;
}

/* Positive doubles order like their bit patterns read as unsigned
 * integers, which are cheaper to compare on the Pico. */
static inline uint64_t bits(double v)
{
    union { double d; uint64_t u; } x;
    x.d = v;
    return x.u;
}

/* ------------------------------------------------------------------------
 * On-sets of the search: the first cnt[g] EVs of each rating group g, i.e.
 * the segments order[gstart[g] .. gstart[g] + cnt[g]). */
typedef struct {
    const int32_t *order;
    int32_t gstart[BIC_MAX_GROUPS + 1];
    int32_t K;
    double xbar[BIC_MAX_GROUPS];   /* rating of each group */
} groups_t;

/* ------------------------------------------------------------------------
 * Per-EV evaluation, as in the Python code. Used when the thresholds of a
 * group are not monotone. */

/* S(lambda) on the mixed domain {0} U [xmin, xmax_i] (calculate_x_lambda,
 * status 0): EV i is on iff lambda < lambda_th[i]. */
static double sum_mixed(double lam, const double *A, const double *CdB,
                        const double *lth, const double *xmax, int32_t n,
                        double xmin)
{
    double s = 0.0;
    for (int32_t i = 0; i < n; i++)
        if (lam < lth[i])
            s += clip(A[i] / lam - CdB[i], xmin, xmax[i]);
    return s;
}

/* Sum of the box allocation clip(A/lam - C/B, xmin, xmax_i) over an on-set
 * (calculate_x_lambda, status 1). */
static double sum_box_set(double lam, const groups_t *G, const int32_t *cnt,
                          const double *A, const double *CdB,
                          const double *xmax, double xmin)
{
    double s = 0.0;
    for (int32_t g = 0; g < G->K; g++)
        for (int32_t k = 0; k < cnt[g]; k++) {
            int32_t i = G->order[G->gstart[g] + k];
            s += clip(A[i] / lam - CdB[i], xmin, xmax[i]);
        }
    return s;
}

/* _restriction: normalized value of the convex restriction on the on-set of
 * the counts cnt, by bisection on lambda over [0, max_i f'_i(xmin)], beyond
 * which every EV of the on-set is at xmin, with the stopping rule of the
 * bisection phase. *lam_out receives the multiplier of the allocation, or 0
 * when the on-set is nonbinding (every EV at its maximum). */
static double restriction_loop(double budget, double eps, const groups_t *G,
                               const int32_t *cnt, const double *A, const double *B,
                               const double *C, const double *D,
                               const double *xmax, double xmin, double *lam_out)
{
    double sx = 0.0, L = -INFINITY;
    for (int32_t g = 0; g < G->K; g++)
        for (int32_t k = 0; k < cnt[g]; k++) {
            int32_t i = G->order[G->gstart[g] + k];
            sx += xmax[i];
            double fp = A[i] * B[i] / (B[i] * xmin + C[i]);
            if (fp > L)
                L = fp;
        }

    double lam_x = 0.0;
    if (!(sx <= budget)) {
        double tol = BIC_DELTA_REL * budget;
        double lo = 0.0, hi = L;
        lam_x = -1.0;
        while (hi - lo > eps) {
            double lam = 0.5 * (lo + hi);
            if (lam == lo || lam == hi)
                break;  /* bracket at floating-point resolution */
            double s = sum_box_set(lam, G, cnt, A, D, xmax, xmin);
            double r = budget - s;
            if (0.0 <= r && r <= tol) {
                lam_x = lam;
                break;
            }
            if (s > budget)
                lo = lam;
            else
                hi = lam;
        }
        if (lam_x < 0.0)
            lam_x = hi;  /* last midpoint with S < budget */
    }
    *lam_out = lam_x;

    double v = 0.0;
    for (int32_t g = 0; g < G->K; g++)
        for (int32_t k = 0; k < cnt[g]; k++) {
            int32_t i = G->order[G->gstart[g] + k];
            double xi = lam_x > 0.0 ? clip(A[i] / lam_x - D[i], xmin, xmax[i])
                                    : xmax[i];
            v += A[i] * (log(B[i] * xi + C[i]) - log(C[i]));
        }
    return v;
}

/* ------------------------------------------------------------------------
 * Sorted evaluation. Thresholds are read in the original order through
 * `order`; prefix sums are in sorted position and restart in each group. */
typedef struct {
    const double *A, *D;          /* A_i and C_i / B_i */
    const double *lo, *hi, *lth;  /* f'(xmin), f'(xmax), lambda_th */
    const double *PA, *PD;        /* prefix sums of A and D */
    const double *PFMIN, *PFMAX;  /* of A log(1 + xmin/D) and A log(1 + xmax/D) */
    const double *PK;             /* of A log(A/D) */
} sorted_t;

/* sum of a prefix-sum array over the sorted positions [u, v) of the group
 * that starts at gs */
static inline double rng(const double *P, int32_t gs, int32_t u, int32_t v)
{
    if (v <= u)
        return 0.0;
    return u > gs ? P[v - 1] - P[u - 1] : P[v - 1];
}

/* first p in [u, v) with key[order[p]] < lam, v if none (key non-increasing
 * along the order, positive) */
static int32_t first_below(const double *key, const int32_t *order,
                           int32_t u, int32_t v, double lam)
{
    uint64_t L = bits(lam);
    while (u < v) {
        int32_t m = (u + v) >> 1;
        if (bits(key[order[m]]) < L) v = m; else u = m + 1;
    }
    return u;
}

/* first p in [u, v) with key[order[p]] <= lam, v if none */
static int32_t first_at_or_below(const double *key, const int32_t *order,
                                 int32_t u, int32_t v, double lam)
{
    uint64_t L = bits(lam);
    while (u < v) {
        int32_t m = (u + v) >> 1;
        if (bits(key[order[m]]) <= L) v = m; else u = m + 1;
    }
    return u;
}

/* S at lam of the on-set with group ends e, given the run boundaries a (end
 * of the xmax run) and b (start of the xmin run) over the whole groups */
static double s_runs(double lam, const int32_t *a, const int32_t *b,
                     const int32_t *e, const groups_t *G, const sorted_t *S,
                     double xmin)
{
    double al = 0.0, be = 0.0;
    int32_t nmin = 0;
    for (int32_t g = 0; g < G->K; g++) {
        int32_t gs = G->gstart[g], eg = e[g];
        if (eg == gs)
            continue;
        int32_t ag = a[g] < eg ? a[g] : eg, bg = b[g] < eg ? b[g] : eg;
        al += rng(S->PA, gs, ag, bg);
        be += (ag - gs) * G->xbar[g] - rng(S->PD, gs, ag, bg);
        nmin += eg - bg;
    }
    return al / lam + be + nmin * xmin;
}

/* closed form S = alpha/lambda + beta of the on-set with group ends e when
 * its run boundaries (clamped to e) are a and b throughout the bracket */
static void closed_form(const int32_t *a, const int32_t *b, const int32_t *e,
                        const groups_t *G, const sorted_t *S, double xmin,
                        double *alpha, double *beta)
{
    double al = 0.0, be = 0.0;
    int32_t nmin = 0;
    for (int32_t g = 0; g < G->K; g++) {
        int32_t gs = G->gstart[g];
        if (e[g] == gs)
            continue;
        al += rng(S->PA, gs, a[g], b[g]);
        be += (a[g] - gs) * G->xbar[g] - rng(S->PD, gs, a[g], b[g]);
        nmin += e[g] - b[g];
    }
    *alpha = al;
    *beta = be + nmin * xmin;
}

/* Remaining steps of a bisection whose S is alpha/lambda + beta on the
 * bracket: the midpoints are compared with lamB (S = budget) and lamT
 * (S = budget - tol). Returns the accepted midpoint, or -1 with *hi set
 * when the bracket collapses. */
static double pinned_steps(double budget, double tol, double eps, double alpha,
                           double beta, double lo, double *hi)
{
    double h = *hi;
    int thr = alpha > 0.0 && budget - tol - beta > 0.0;
    double lamB = thr ? alpha / (budget - beta) : 0.0;
    double lamT = thr ? alpha / (budget - tol - beta) : 0.0;
    while (bits(h - lo) > bits(eps)) {
        double m = 0.5 * (lo + h);
        if (bits(m) == bits(lo) || bits(m) == bits(h))
            break;
        if (thr) {
            if (bits(m) < bits(lamB))
                lo = m;
            else if (bits(m) <= bits(lamT))
                return m;
            else
                h = m;
            continue;
        }
        double s = alpha / m + beta, r = budget - s;
        if ((bits(r) >> 63) == 0 && bits(r) <= bits(tol))
            return m;
        if (bits(s) > bits(budget))
            lo = m;
        else
            h = m;
    }
    *hi = h;
    return -1.0;
}

/* Everett fast path on the sorted structure (bisection_phase, status 0).
 * Returns the accepted multiplier and the number of EVs switched on in each
 * group, or -1 when the bracket collapses (an Everett gap). */
static double fast_sorted(double budget, double eps, double L, const groups_t *G,
                          const sorted_t *S, double xmin, int32_t *cnt)
{
    const int32_t K = G->K;
    const int32_t *order = G->order;
    /* index brackets of the runs: the index at the upper end of the lambda
     * bracket (H) is a lower bound and at the lower end (L) an upper bound
     * for any lambda inside; o: on-set end, a: xmax run end, b: xmin run
     * start */
    int32_t oH[BIC_MAX_GROUPS], oL[BIC_MAX_GROUPS], aH[BIC_MAX_GROUPS],
            aL[BIC_MAX_GROUPS], bH[BIC_MAX_GROUPS], bL[BIC_MAX_GROUPS];
    int32_t o[BIC_MAX_GROUPS], a[BIC_MAX_GROUPS], b[BIC_MAX_GROUPS];
    for (int32_t g = 0; g < K; g++) {
        oH[g] = aH[g] = bH[g] = G->gstart[g];
        oL[g] = aL[g] = bL[g] = G->gstart[g + 1];
    }
    const double tol = BIC_DELTA_REL * budget;
    double lo = 0.0, hi = L;
    while (bits(hi - lo) > bits(eps)) {
        double lam = 0.5 * (lo + hi);
        if (bits(lam) == bits(lo) || bits(lam) == bits(hi))
            break;
        for (int32_t g = 0; g < K; g++) {
            o[g] = first_at_or_below(S->lth, order, oH[g], oL[g], lam);
            a[g] = first_below(S->hi, order, aH[g], aL[g] < o[g] ? aL[g] : o[g], lam);
            int32_t u = bH[g] > a[g] ? bH[g] : a[g], v = bL[g] < o[g] ? bL[g] : o[g];
            b[g] = first_at_or_below(S->lo, order, u, v < u ? u : v, lam);
        }
        double s = s_runs(lam, a, b, o, G, S, xmin), r = budget - s;
        if ((bits(r) >> 63) == 0 && bits(r) <= bits(tol)) {
            for (int32_t g = 0; g < K; g++)
                cnt[g] = o[g] - G->gstart[g];
            return lam;
        }
        int32_t *O = oL, *Ar = aL, *Br = bL;
        if (bits(s) > bits(budget))
            lo = lam;
        else {
            hi = lam;
            O = oH;
            Ar = aH;
            Br = bH;
        }
        int pinned = 1;
        for (int32_t g = 0; g < K; g++) {
            O[g] = o[g];
            Ar[g] = a[g];
            Br[g] = b[g];
            if (oH[g] != oL[g] || aH[g] != aL[g] || bH[g] != bL[g])
                pinned = 0;
        }
        if (pinned) {
            /* no threshold inside the bracket: the on-set and the runs are
             * fixed, and S = alpha/lambda + beta */
            double alpha, beta;
            closed_form(aH, bH, oH, G, S, xmin, &alpha, &beta);
            double lam_p = pinned_steps(budget, tol, eps, alpha, beta, lo, &hi);
            if (lam_p > 0.0)
                for (int32_t g = 0; g < K; g++)
                    cnt[g] = oH[g] - G->gstart[g];
            return lam_p;
        }
    }
    return -1.0;
}

/* Stored bisection path of the restrictions of one solve. At depth k: the
 * midpoint m[k], S[k] for the on-set with group ends own[k], the run
 * boundaries ia, ib over the whole groups at m[k] (they do not depend on the
 * on-set), the decision dec[k] (0: S > budget, 1: S < budget - tol, 2:
 * accepted) that leads to depth k + 1, and two caps: removing at most
 * cap_lo[k] EVs keeps S > budget, adding at most cap_hi[k] EVs keeps
 * S < budget - tol (-1: no such guarantee). */
#define BIC_PATH_DEPTH 64
static struct {
    int valid;
    uint64_t Lbits;
    int32_t len;
    double m[BIC_PATH_DEPTH], S[BIC_PATH_DEPTH];
    int32_t cap_lo[BIC_PATH_DEPTH], cap_hi[BIC_PATH_DEPTH];
    int16_t own[BIC_PATH_DEPTH][BIC_MAX_GROUPS];
    int16_t ia[BIC_PATH_DEPTH][BIC_MAX_GROUPS], ib[BIC_PATH_DEPTH][BIC_MAX_GROUPS];
    int8_t dec[BIC_PATH_DEPTH];
} g_path;

/* ixb = (1 - 1e-12) / (largest rating); caps are limited to 2^20 */
static void set_caps(int32_t k, double s, double budget, double tol, double ixb)
{
    double M = s - budget, H = budget - tol - s;
    double cl = M * ixb, ch = H * ixb;
    g_path.cap_lo[k] = (bits(M) >> 63) || M == 0.0 ? -1
                     : bits(cl) > bits(1048576.0) ? 1048576 : (int32_t)cl;
    g_path.cap_hi[k] = (bits(H) >> 63) || H == 0.0 ? -1
                     : bits(ch) > bits(1048576.0) ? 1048576 : (int32_t)ch;
}

/* _restriction on the sorted structure, following the stored path. Same
 * return values as restriction_loop. */
static double restriction_sorted(double budget, double eps, const groups_t *G,
                                 const sorted_t *S, const int32_t *cnt, double xmin,
                                 double *lam_out)
{
    const int32_t K = G->K;
    const int32_t *order = G->order;
    int32_t e[BIC_MAX_GROUPS], fe[BIC_MAX_GROUPS];
    int32_t aH[BIC_MAX_GROUPS], bH[BIC_MAX_GROUPS], aL[BIC_MAX_GROUPS], bL[BIC_MAX_GROUPS];
    int32_t pa[BIC_MAX_GROUPS], pb[BIC_MAX_GROUPS];
    double sx = 0.0, L = -INFINITY, xbmax = 0.0;
    for (int32_t g = 0; g < K; g++) {
        int32_t gs = G->gstart[g];
        e[g] = gs + cnt[g];
        fe[g] = G->gstart[g + 1];
        aH[g] = bH[g] = gs;
        aL[g] = bL[g] = fe[g];
        if (G->xbar[g] > xbmax)
            xbmax = G->xbar[g];
        if (cnt[g] > 0) {
            sx += cnt[g] * G->xbar[g];
            if (S->lo[order[gs]] > L)
                L = S->lo[order[gs]];
        }
    }
    double v = 0.0;
    if (sx <= budget) {
        *lam_out = 0.0;
        for (int32_t g = 0; g < K; g++)
            v += rng(S->PFMAX, G->gstart[g], G->gstart[g], e[g]);
        return v;
    }

    const double tol = BIC_DELTA_REL * budget;
    const double ixb = (1.0 - 1e-12) / xbmax;
    double lo = 0.0, hi = L, lam_x = -1.0;
    int idx_known = 0, hi_exact = 0;
    int on_path = g_path.valid && g_path.Lbits == bits(L);
    if (!on_path) {
        g_path.valid = 1;
        g_path.Lbits = bits(L);
        g_path.len = 0;
    }
    int32_t k = 0;

    for (;;) {
        int d;
        if (on_path && k < g_path.len) {
            /* Stored steps: the stored decision holds when the caps allow
             * the EVs that differ from the on-set of the stored S. */
            int32_t kk = k, klo = -1, khi = -1;
            while (kk < g_path.len) {
                int32_t n_add = 0, n_rem = 0;
                for (int32_t g = 0; g < K; g++) {
                    int32_t df = e[g] - g_path.own[kk][g];
                    if (df > 0) n_add += df; else n_rem -= df;
                }
                if (n_rem <= g_path.cap_lo[kk]) d = 0;
                else if (n_add <= g_path.cap_hi[kk]) d = 1;
                else break;
                if (d != g_path.dec[kk])
                    break;
                if (d == 0) klo = kk; else khi = kk;
                kk++;
            }
            if (klo >= 0) {
                lo = g_path.m[klo];
                for (int32_t g = 0; g < K; g++) { aL[g] = g_path.ia[klo][g]; bL[g] = g_path.ib[klo][g]; }
            }
            if (khi >= 0) {
                hi = g_path.m[khi];
                hi_exact = 1;
                for (int32_t g = 0; g < K; g++) { aH[g] = g_path.ia[khi][g]; bH[g] = g_path.ib[khi][g]; }
            }
            k = kk;
            if (k < g_path.len) {
                /* the caps do not decide, or the decision leaves the path */
                double m = g_path.m[k];
                int32_t n_add = 0, n_rem = 0;
                for (int32_t g = 0; g < K; g++) {
                    int32_t df = e[g] - g_path.own[k][g];
                    if (df > 0) n_add += df; else n_rem -= df;
                }
                double Sk = g_path.S[k];
                d = -1;
                if (n_add + n_rem <= 8) {
                    /* the EVs that differ change S by between
                     * n_add*xmin - n_rem*xbmax and n_add*xbmax - n_rem*xmin */
                    if (Sk > budget - n_add * xmin + n_rem * xbmax)
                        d = 0;
                    else if (Sk < budget - tol - n_add * xbmax + n_rem * xmin)
                        d = 1;
                }
                if (d < 0) {
                    double s;
                    if (n_add + n_rem <= 8) {
                        /* the stored S corrected by the EVs that differ; their
                         * run at m follows from the stored boundaries */
                        s = Sk;
                        for (int32_t g = 0; g < K; g++) {
                            int32_t ow = g_path.own[k][g], eg = e[g];
                            int32_t p0 = ow < eg ? ow : eg, p1 = ow < eg ? eg : ow;
                            for (int32_t p = p0; p < p1; p++) {
                                double xp;
                                if (p < g_path.ia[k][g])
                                    xp = G->xbar[g];
                                else if (p >= g_path.ib[k][g])
                                    xp = xmin;
                                else
                                    xp = S->A[order[p]] / m - S->D[order[p]];
                                s = eg > ow ? s + xp : s - xp;
                            }
                        }
                    } else {
                        int32_t ia[BIC_MAX_GROUPS], ib[BIC_MAX_GROUPS];
                        for (int32_t g = 0; g < K; g++) {
                            ia[g] = g_path.ia[k][g];
                            ib[g] = g_path.ib[k][g];
                        }
                        s = s_runs(m, ia, ib, e, G, S, xmin);
                    }
                    g_path.S[k] = s;
                    set_caps(k, s, budget, tol, ixb);
                    for (int32_t g = 0; g < K; g++)
                        g_path.own[k][g] = (int16_t)e[g];
                    double r = budget - s;
                    if ((bits(r) >> 63) == 0 && bits(r) <= bits(tol)) {
                        lam_x = m;
                        for (int32_t g = 0; g < K; g++) {
                            pa[g] = g_path.ia[k][g] < e[g] ? g_path.ia[k][g] : e[g];
                            pb[g] = g_path.ib[k][g] < e[g] ? g_path.ib[k][g] : e[g];
                        }
                        idx_known = 1;
                        g_path.dec[k] = 2;
                        g_path.len = k + 1;
                        break;
                    }
                    d = bits(s) > bits(budget) ? 0 : 1;
                }
                if (d == 0) {
                    lo = m;
                    for (int32_t g = 0; g < K; g++) { aL[g] = g_path.ia[k][g]; bL[g] = g_path.ib[k][g]; }
                } else {
                    hi = m;
                    hi_exact = 1;
                    for (int32_t g = 0; g < K; g++) { aH[g] = g_path.ia[k][g]; bH[g] = g_path.ib[k][g]; }
                }
                if (d != g_path.dec[k]) {
                    g_path.dec[k] = (int8_t)d;
                    g_path.len = k + 1;
                    on_path = 0;
                }
                k++;
            }
        } else {
            /* a new step: runs by narrowed searches, S, stored at depth k */
            if (!(bits(hi - lo) > bits(eps)))
                break;
            double m = 0.5 * (lo + hi);
            if (bits(m) == bits(lo) || bits(m) == bits(hi))
                break;
            on_path = 0;
            int32_t ia[BIC_MAX_GROUPS], ib[BIC_MAX_GROUPS];
            for (int32_t g = 0; g < K; g++) {
                ia[g] = first_below(S->hi, order, aH[g], aL[g], m);
                int32_t u = bH[g] > ia[g] ? bH[g] : ia[g], w = bL[g] > u ? bL[g] : u;
                ib[g] = first_at_or_below(S->lo, order, u, w, m);
            }
            double s = s_runs(m, ia, ib, e, G, S, xmin), r = budget - s;
            int store = k < BIC_PATH_DEPTH;
            if (store) {
                g_path.m[k] = m;
                g_path.S[k] = s;
                set_caps(k, s, budget, tol, ixb);
                for (int32_t g = 0; g < K; g++) {
                    g_path.own[k][g] = (int16_t)e[g];
                    g_path.ia[k][g] = (int16_t)ia[g];
                    g_path.ib[k][g] = (int16_t)ib[g];
                }
                g_path.len = k + 1;
            }
            if ((bits(r) >> 63) == 0 && bits(r) <= bits(tol)) {
                lam_x = m;
                for (int32_t g = 0; g < K; g++) {
                    pa[g] = ia[g] < e[g] ? ia[g] : e[g];
                    pb[g] = ib[g] < e[g] ? ib[g] : e[g];
                }
                idx_known = 1;
                if (store)
                    g_path.dec[k] = 2;
                break;
            }
            d = bits(s) > bits(budget) ? 0 : 1;
            if (store)
                g_path.dec[k] = (int8_t)d;
            if (d == 0) {
                lo = m;
                for (int32_t g = 0; g < K; g++) { aL[g] = ia[g]; bL[g] = ib[g]; }
            } else {
                hi = m;
                hi_exact = 1;
                for (int32_t g = 0; g < K; g++) { aH[g] = ia[g]; bH[g] = ib[g]; }
            }
            k++;
        }

        /* pinned when no threshold of the on-set lies inside the bracket */
        int pinned = 1;
        for (int32_t g = 0; g < K && pinned; g++) {
            int32_t eg = e[g];
            if (eg == G->gstart[g])
                continue;
            if ((aH[g] < eg ? aH[g] : eg) != (aL[g] < eg ? aL[g] : eg)
                || (bH[g] < eg ? bH[g] : eg) != (bL[g] < eg ? bL[g] : eg))
                pinned = 0;
        }
        if (pinned) {
            for (int32_t g = 0; g < K; g++) {
                pa[g] = aH[g] < e[g] ? aH[g] : e[g];
                pb[g] = bH[g] < e[g] ? bH[g] : e[g];
            }
            idx_known = 1;
            double alpha, beta;
            closed_form(pa, pb, e, G, S, xmin, &alpha, &beta);
            lam_x = pinned_steps(budget, tol, eps, alpha, beta, lo, &hi);
            break;
        }
    }
    if (lam_x < 0.0) {
        lam_x = hi;  /* last midpoint with S < budget */
        if (!idx_known) {
            for (int32_t g = 0; g < K; g++) {
                int32_t gs = G->gstart[g];
                if (hi_exact) {
                    pa[g] = aH[g] < e[g] ? aH[g] : e[g];
                    pb[g] = bH[g] < e[g] ? bH[g] : e[g];
                } else {
                    pa[g] = first_below(S->hi, order, gs, e[g], lam_x);
                    pb[g] = first_at_or_below(S->lo, order, pa[g], e[g], lam_x);
                }
            }
        }
    }
    *lam_out = lam_x;

    /* value: f at xmax on the xmax run, A (log(A/D) - log lambda) on the
     * interior run, f at xmin on the xmin run (f normalized, f(0) = 0) */
    double lg = log(lam_x);
    for (int32_t g = 0; g < K; g++) {
        int32_t gs = G->gstart[g];
        if (e[g] == gs)
            continue;
        v += rng(S->PFMAX, gs, gs, pa[g]) + rng(S->PK, gs, pa[g], pb[g])
             - lg * rng(S->PA, gs, pa[g], pb[g]) + rng(S->PFMIN, gs, pb[g], e[g]);
    }
    return v;
}

/* ------------------------------------------------------------------------
 * Priority order (dominance_order in bic/bic.py) within each rating group:
 * rating ascending (np.unique),
 * then f'(0+) descending, ties by f'(xmax) descending, ties by index
 * (np.lexsort is stable). The EVs are split by rating, and each group is
 * merge sorted on (bits of f'(0+), index) pairs. */
static void merge_sort_group(uint64_t *key, int32_t *idx, uint64_t *kt, int32_t *it,
                             int32_t n, const double *fpx)
{
    uint64_t *ks = key, *kd = kt;
    int32_t *is = idx, *id = it;
    for (int32_t w = 1; w < n; w *= 2) {
        for (int32_t lo = 0; lo < n; lo += 2 * w) {
            int32_t mid = lo + w < n ? lo + w : n, hi = lo + 2 * w < n ? lo + 2 * w : n;
            int32_t i = lo, j = mid, k = lo;
            while (i < mid && j < hi) {
                int right;
                if (ks[j] != ks[i])
                    right = ks[j] > ks[i];
                else {
                    uint64_t a = bits(fpx[is[j]]), b = bits(fpx[is[i]]);
                    right = a != b ? a > b : is[j] < is[i];
                }
                if (right) { kd[k] = ks[j]; id[k++] = is[j++]; }
                else { kd[k] = ks[i]; id[k++] = is[i++]; }
            }
            while (i < mid) { kd[k] = ks[i]; id[k++] = is[i++]; }
            while (j < hi) { kd[k] = ks[j]; id[k++] = is[j++]; }
        }
        uint64_t *t = ks; ks = kd; kd = t;
        int32_t *u = is; is = id; id = u;
    }
    if (is != idx)
        memcpy(idx, is, (size_t)n * sizeof(int32_t));
}

/* Indexing phase. fp0 and fpx receive the sort keys f'(0+) and f'(xmax)
 * (original order); key, kt and it are scratch of n elements. */
static int index_phase(const double *A, const double *B, const double *C,
                       const double *xmax, int32_t n, double *fp0, double *fpx,
                       uint64_t *key, uint64_t *kt, int32_t *it,
                       int32_t *order, groups_t *G, bic_result_t *res)
{
    for (int32_t i = 0; i < n; i++) {
        double ab = A[i] * B[i];
        fp0[i] = ab / C[i];
        fpx[i] = ab / (B[i] * xmax[i] + C[i]);
    }

    /* distinct ratings, ascending, then a stable split into the groups */
    uint64_t vb[BIC_MAX_GROUPS];
    int32_t K = 0, cntg[BIC_MAX_GROUPS] = {0}, pos[BIC_MAX_GROUPS];
    for (int32_t i = 0; i < n; i++) {
        uint64_t b = bits(xmax[i]);
        int32_t g = 0;
        while (g < K && vb[g] != b)
            g++;
        if (g == K) {
            if (K == BIC_MAX_GROUPS)
                return BIC_ERR_GROUPS;
            int32_t q = K++;
            while (q > 0 && vb[q - 1] > b) {
                vb[q] = vb[q - 1];
                q--;
            }
            vb[q] = b;
        }
    }
    for (int32_t i = 0; i < n; i++) {
        uint64_t b = bits(xmax[i]);
        int32_t g = 0;
        while (vb[g] != b)
            g++;
        it[i] = g;
        cntg[g]++;
    }
    G->order = order;
    G->K = K;
    int32_t p0 = 0;
    for (int32_t g = 0; g < K; g++) {
        G->gstart[g] = pos[g] = p0;
        p0 += cntg[g];
    }
    G->gstart[K] = n;
    for (int32_t i = 0; i < n; i++)
        order[pos[it[i]]++] = i;
    for (int32_t g = 0; g < K; g++)
        G->xbar[g] = xmax[order[G->gstart[g]]];
    for (int32_t p = 0; p < n; p++)
        key[p] = bits(fp0[order[p]]);
    for (int32_t g = 0; g < K; g++) {
        int32_t gs = G->gstart[g];
        merge_sort_group(key + gs, order + gs, kt + gs, it + gs,
                         G->gstart[g + 1] - gs, fpx);
    }

    /* priority order check; a difference can exceed the tolerance only
     * where the key rises */
    const double chain_tol = 1e-12;
    for (int32_t g = 0; g < K && res->chain_ok; g++)
        for (int32_t k = G->gstart[g]; k + 1 < G->gstart[g + 1]; k++) {
            int32_t i = order[k], j = order[k + 1];
            if ((bits(fp0[j]) > bits(fp0[i]) && fp0[j] - fp0[i] > chain_tol)
                || (bits(fpx[j]) > bits(fpx[i]) && fpx[j] - fpx[i] > chain_tol)) {
                res->chain_ok = 0;
                break;
            }
        }
    return BIC_OK;
}

/* f'(xmin) (original order) and the prefix sums of A and D for the sorted
 * evaluation. Returns 1 if f'(xmin), f'(xmax) and, when given, lambda_th are
 * non-increasing along the order within every group. */
static int bisection_data(const double *A, const double *B, const double *C,
                          const double *D, const double *hi, const double *lth,
                          double xmin, const groups_t *G, double *lo,
                          double *PA, double *PD, int32_t n)
{
    for (int32_t i = 0; i < n; i++)
        lo[i] = A[i] * B[i] / (B[i] * xmin + C[i]);
    int mono = 1;
    for (int32_t g = 0; g < G->K; g++) {
        double pa = 0.0, pd = 0.0;
        for (int32_t p = G->gstart[g]; p < G->gstart[g + 1]; p++) {
            int32_t i = G->order[p];
            PA[p] = pa += A[i];
            PD[p] = pd += D[i];
            if (p > G->gstart[g]) {
                int32_t j = G->order[p - 1];
                if (bits(lo[i]) > bits(lo[j]) || bits(hi[i]) > bits(hi[j])
                    || (lth && bits(lth[i]) > bits(lth[j])))
                    mono = 0;
            }
        }
    }
    return mono;
}

/* prefix sums of the values: A log(1 + xmin/D) (from lambda_th when it was
 * computed), A log(1 + xmax/D) and A log(A/D). PFMIN is first built in PK
 * and then copied to its place, which may be lambda_th's array. */
static void value_data(const double *A, const double *D, const double *lth,
                       double xmin, const groups_t *G, double *PFMIN,
                       double *PFMAX, double *PK, int32_t n)
{
    for (int32_t g = 0; g < G->K; g++) {
        double s = 0.0;
        for (int32_t p = G->gstart[g]; p < G->gstart[g + 1]; p++) {
            int32_t i = G->order[p];
            PK[p] = s += lth ? lth[i] * xmin : A[i] * log1p(xmin / D[i]);
        }
    }
    memcpy(PFMIN, PK, (size_t)n * sizeof(double));
    for (int32_t g = 0; g < G->K; g++) {
        double xb = G->xbar[g], smax = 0.0, sk = 0.0;
        for (int32_t p = G->gstart[g]; p < G->gstart[g + 1]; p++) {
            int32_t i = G->order[p];
            double a = A[i], d = D[i];
            PFMAX[p] = smax += a * log1p(xb / d);
            PK[p] = sk += a * log(a / d);
        }
    }
}

int bic_solve(double budget, double eps,
              const double *A, const double *B, const double *C,
              const double *xmax, int32_t n, double xmin,
              int32_t fastpath,
              double *x, double *work, int32_t *order, bic_result_t *res)
{
    const double tol = 1e-6;

    res->path = BIC_PATH_ALL_MAX;
    res->c_best = 0;
    res->chain_ok = 1;
    res->n_groups = 0;
    res->lam = 0.0;
    res->objval = 0.0;

    if (n < 0 || n > 32767 || !(xmin > 0.0) || !(budget >= 0.0) || !(eps > 0.0))
        return BIC_ERR_INPUT;
    for (int32_t i = 0; i < n; i++)
        if (!(A[i] > 0.0) || !(B[i] > 0.0) || !(C[i] > 0.0)
            || !(xmax[i] >= xmin))
            return BIC_ERR_INPUT;

    /* Nonbinding budget shortcut */
    double sum_xmax = 0.0;
    for (int32_t i = 0; i < n; i++)
        sum_xmax += xmax[i];
    if (sum_xmax <= budget) {
        for (int32_t i = 0; i < n; i++)
            x[i] = xmax[i];
        res->c_best = n;
        goto finish;
    }

    {
        /* workspace: D = C/B, lambda_th (later the prefix sums of f at
         * xmin), f'(xmax), then four prefix-sum arrays; x holds f'(0+) and
         * then f'(xmin) until the allocation is written */
        double *D = work, *lth = work + n, *fpx = work + 2 * n;
        double *PA = work + 3 * n, *PD = work + 4 * n;
        double *PFMAX = work + 5 * n, *PK = work + 6 * n;
        double *fp0 = x, *lo = x;
        double L = -INFINITY;

        /* lambda_th = f(xmin) / xmin with f normalized, f(0) = 0 */
        const double ixm = 1.0 / xmin;
        for (int32_t i = 0; i < n; i++) {
            D[i] = C[i] / B[i];
            if (fastpath) {
                lth[i] = A[i] * log1p(xmin / D[i]) * ixm;
                if (lth[i] > L)
                    L = lth[i];
            }
        }

        /* Indexing phase, before the fast path, so that it can use the
         * sorted evaluation too */
        groups_t G;
        int rc = index_phase(A, B, C, xmax, n, fp0, fpx, (uint64_t *)PFMAX,
                             (uint64_t *)PK, (int32_t *)PA, order, &G, res);
        if (rc != BIC_OK)
            return rc;
        int mono = bisection_data(A, B, C, D, fpx, fastpath ? lth : NULL, xmin,
                                  &G, lo, PA, PD, n);
        sorted_t S = {A, D, lo, fpx, lth, PA, PD, NULL, PFMAX, PK};

        /* Everett fast path (bisection_phase) */
        if (fastpath) {
            int32_t on = 0, cnt[BIC_MAX_GROUPS];
            double lam = -1.0;
            if (mono) {
                lam = fast_sorted(budget, eps, L, &G, &S, xmin, cnt);
                if (lam > 0.0) {
                    for (int32_t i = 0; i < n; i++)
                        x[i] = 0.0;
                    for (int32_t g = 0; g < G.K; g++)
                        for (int32_t p = G.gstart[g]; p < G.gstart[g] + cnt[g]; p++) {
                            int32_t i = order[p];
                            x[i] = clip(A[i] / lam - D[i], xmin, xmax[i]);
                            on++;
                        }
                }
            } else {
                double tol_b = BIC_DELTA_REL * budget;
                double lo_b = 0.0, hi_b = L;
                while (hi_b - lo_b > eps) {
                    double m = 0.5 * (lo_b + hi_b);
                    if (m == lo_b || m == hi_b)
                        break;
                    double s = sum_mixed(m, A, D, lth, xmax, n, xmin);
                    double r = budget - s;
                    if (0.0 <= r && r <= tol_b) {
                        lam = m;
                        for (int32_t i = 0; i < n; i++) {
                            if (m < lth[i]) {
                                x[i] = clip(A[i] / m - D[i], xmin, xmax[i]);
                                on++;
                            } else {
                                x[i] = 0.0;
                            }
                        }
                        break;
                    }
                    if (s > budget)
                        lo_b = m;
                    else
                        hi_b = m;
                }
            }
            if (lam > 0.0) {
                res->path = BIC_PATH_FAST;
                res->lam = lam;
                res->c_best = on;
                goto finish;
            }
        }

        /* Choosing phase (_choosing_phase): with one group, a binary search
         * on the count; with more, the counts of all groups but the last two
         * are enumerated and a monotone walk runs over the last two. Each
         * value is computed once, as with the cache of the Python code,
         * except in the binary search, where recomputing gives the same
         * value. c_max uses the tolerance of the feasibility test. */
        int32_t K = G.K;
        if (mono) {
            value_data(A, D, fastpath ? lth : NULL, xmin, &G, lth, PFMAX, PK, n);
            S.PFMIN = lth;
            g_path.valid = 0;
        }
#define RESTRICT(lamp) \
    (mono ? restriction_sorted(budget, eps, &G, &S, cnt, xmin, (lamp)) \
          : restriction_loop(budget, eps, &G, cnt, A, B, C, D, xmax, xmin, (lamp)))

        int32_t c_max = (int32_t)floor(budget / xmin + 1e-12);
        int32_t cnt[BIC_MAX_GROUPS] = {0}, best_cnt[BIC_MAX_GROUPS] = {0};
        double best_lam = 0.0, lam;
#define GSIZE(g) (G.gstart[(g) + 1] - G.gstart[(g)])
        if (K == 1) {
            int32_t lo_c = 0, hi_c = GSIZE(0) < c_max ? GSIZE(0) : c_max;
            while (lo_c < hi_c) {
                int32_t mid = (lo_c + hi_c) / 2;
                cnt[0] = mid + 1;
                double v_up = RESTRICT(&lam);
                cnt[0] = mid;
                double v_mid = RESTRICT(&lam);
                if (v_up > v_mid)
                    lo_c = mid + 1;
                else
                    hi_c = mid;
            }
            best_cnt[0] = cnt[0] = lo_c;
            RESTRICT(&best_lam);
        } else {
            double V_best = -INFINITY;
            int32_t ga = K - 2, gb = K - 1;
            int32_t n_a = GSIZE(ga), n_b = GSIZE(gb);
            /* itertools.product over the counts of groups 0 .. K-3, with the
             * last of them varying fastest (one empty tuple for K = 2). */
            for (;;) {
                int32_t used = 0;
                for (int32_t g = 0; g < ga; g++)
                    used += cnt[g];
                int32_t room = c_max - used;
                if (room >= 0) {
                    int32_t t = n_b < room ? n_b : room;
                    int32_t a_max = n_a < room ? n_a : room;
                    for (int32_t c_a = 0; c_a <= a_max; c_a++) {
                        if (t > room - c_a)
                            t = room - c_a;
                        cnt[ga] = c_a;
                        cnt[gb] = t;
                        double lam_t, v_t = RESTRICT(&lam_t);
                        /* lower the count of the last group while one EV
                         * fewer gives at least the same value */
                        while (t > 0) {
                            cnt[gb] = t - 1;
                            double lam_p, v_p = RESTRICT(&lam_p);
                            if (!(v_p >= v_t))
                                break;
                            t--;
                            v_t = v_p;
                            lam_t = lam_p;
                        }
                        cnt[gb] = t;
                        if (v_t > V_best) {
                            V_best = v_t;
                            best_lam = lam_t;
                            for (int32_t g = 0; g < K; g++)
                                best_cnt[g] = cnt[g];
                        }
                    }
                    cnt[ga] = cnt[gb] = 0;
                }
                /* next tuple of counts for groups 0 .. K-3 */
                int32_t g = ga - 1;
                while (g >= 0) {
                    if (cnt[g] < GSIZE(g)) {
                        cnt[g]++;
                        break;
                    }
                    cnt[g] = 0;
                    g--;
                }
                if (g < 0)
                    break;
            }
        }
#undef GSIZE
#undef RESTRICT

        for (int32_t i = 0; i < n; i++)
            x[i] = 0.0;
        int32_t on = 0;
        for (int32_t g = 0; g < K; g++)
            for (int32_t k = 0; k < best_cnt[g]; k++) {
                int32_t i = order[G.gstart[g] + k];
                x[i] = best_lam > 0.0 ? clip(A[i] / best_lam - D[i], xmin, xmax[i])
                                      : xmax[i];
                on++;
            }
        res->path = BIC_PATH_CHOOSE;
        res->c_best = on;
        res->n_groups = K;
        res->lam = best_lam;
    }

finish:
    {
        /* objective sum_i A_i log(B_i x_i + C_i): one log per distinct A_i,
         * of the product of B_i x_i + C_i kept as mantissa and exponent;
         * with more than 8 distinct A_i, one log per EV */
        double obj = 0.0, total = 0.0;
        uint64_t vb[8];
        double val[8], mant[8];
        int32_t ex[8], nv = 0;
        int prod = 1;
        for (int32_t i = 0; i < n && prod; i++) {
            uint64_t b = bits(A[i]);
            int32_t k = 0;
            while (k < nv && vb[k] != b)
                k++;
            if (k == nv) {
                if (nv == 8) {
                    prod = 0;
                    break;
                }
                vb[nv] = b;
                val[nv] = A[i];
                mant[nv] = 1.0;
                ex[nv++] = 0;
            }
            double m = mant[k] * (B[i] * x[i] + C[i]);
            if (m > 1e150 || m < 1e-150) {
                int e;
                m = frexp(m, &e);
                ex[k] += e;
            }
            mant[k] = m;
        }
        if (prod)
            for (int32_t k = 0; k < nv; k++)
                obj += val[k] * (log(mant[k]) + ex[k] * 0.69314718055994530942);
        for (int32_t i = 0; i < n; i++) {
            if (!prod)
                obj += A[i] * log(B[i] * x[i] + C[i]);
            total += x[i];
            int ok = fabs(x[i]) <= tol
                     || (x[i] >= xmin - tol && x[i] <= xmax[i] + tol);
            if (!ok)
                return BIC_ERR_RESULT;
        }
        if (total > budget + tol)
            return BIC_ERR_RESULT;
        res->objval = obj;
    }
    return BIC_OK;
}
