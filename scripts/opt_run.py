"""Fig. 1 data: optimality ratio of BIC, HB1 and HB2 against the MIP on
HB1- and HB2-adversarial instances.

Output: results/opt_instances.csv, results/opt_cells.csv (median per cell)
"""
import os
import sys
import warnings

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import bic

XMIN, XMAX = 4.16, 11.0
N = 100
EPS = 1e-13
ELL_T = 20.0
MARGIN = 0.05
HB1_EDGE_FRACTION = 0.01
REPS = 10
RHOS = [0.10, 0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.80]
PCTS = [0, 20, 40, 60, 80, 100]
MIP_TIME_LIMIT = 10.0
METHODS = ['BIC', 'HB1', 'HB2']
HEURISTICS = ['HB1', 'HB2']
RATINGS = np.asarray(bic.RATINGS_KW)


def lam_th_mr(m, r):
    """Switching threshold of an sLLF EV with laxity m + 1 and rating r."""
    return (r / XMIN) * np.log1p((XMIN / r) / m)


def make_h1_instance(B, n, K, ell_T, seed):
    """K EVs tied at laxity ell_T, one rating, whose Everett jump straddles B.
    The power of the other EVs sits near the lower edge of the jump, so HB1
    switches off the whole tied block."""
    rng = np.random.default_rng(seed)
    mT = ell_T - 1.0
    r_T = float(rng.choice(RATINGS))
    lamT = lam_th_mr(mT, r_T)
    n_avail = n - K
    r_free = rng.choice(RATINGS, n_avail)
    lo_c = XMIN + MARGIN

    if K == 0:
        win_lo, win_hi = B, B
    else:
        win_lo, win_hi = B - K * XMIN, B
    margin = max(1e-6 * max(B, 1.0), 1e-9) if K > 0 else 0.0
    s_lo = max(win_lo + margin, 0.0)
    s_hi = min(win_hi - margin, float(np.sum(r_free - MARGIN)))
    if s_lo > s_hi:
        raise ValueError
    S_bg = s_lo + HB1_EDGE_FRACTION * (s_hi - s_lo)

    def off_laxities(r_off):
        m_off = rng.uniform(mT * 1.05, mT * 2.0, len(r_off))
        if np.any(lam_th_mr(m_off, r_off) >= lamT):
            raise ValueError
        return m_off

    if S_bg < lo_c:
        m_off = off_laxities(r_free)
        return (np.concatenate([np.full(K, ell_T), m_off + 1.0]),
                np.concatenate([np.full(K, r_T), r_free]))

    hi_all = r_free - MARGIN
    guess = int(round(S_bg / (0.5 * (lo_c + np.mean(hi_all)))))
    n_on = None
    for cand in sorted(range(1, n_avail + 1), key=lambda c: abs(c - guess)):
        if cand * lo_c <= S_bg <= np.sum(hi_all[:cand]):
            n_on = cand
            break
    if n_on is None:
        raise ValueError
    r_on, r_off = r_free[:n_on], r_free[n_on:]
    hi_c = r_on - MARGIN
    t = (S_bg - n_on * lo_c) / np.sum(hi_c - lo_c)
    c = lo_c + t * (hi_c - lo_c)
    d = rng.uniform(-1, 1, n_on)
    d -= d.mean()
    room = np.minimum(c - lo_c, hi_c - c)
    if np.min(room) > 0 and np.max(np.abs(d)) > 0:
        c = c + d * 0.9 * np.min(room) / np.max(np.abs(d))

    m_on = 1.0 / lamT - c / r_on
    if not np.all(m_on > 0):
        raise ValueError
    m_off = off_laxities(r_off)
    return (np.concatenate([np.full(K, ell_T), m_on + 1.0, m_off + 1.0]),
            np.concatenate([np.full(K, r_T), r_on, r_off]))


def build_h1(B, n, K, seed, max_tries=40):
    for t in range(max_tries):
        try:
            lax, xmax = make_h1_instance(B, n, K, ELL_T, seed=1000 * seed + t)
            perm = np.random.default_rng(seed).permutation(n)
            return lax[perm], xmax[perm]
        except ValueError:
            continue
    return None


def build_h2(B, n, K, seed):
    """Saturated urgent EVs, K tied EVs whose jump straddles B, and decoys
    with large laxities, which HB2 switches on."""
    rng = np.random.default_rng(seed)
    r_T = float(rng.choice(RATINGS))
    n_free = n - K
    r_free = rng.choice(RATINGS, n_free)
    cs = np.cumsum(r_free)
    if K == 0:
        hit = np.nonzero(cs >= B - 1e-12)[0]
        if len(hit) == 0:
            return None
        n_urgent = int(hit[0]) + 1
    else:
        n_urgent = int(np.sum(cs < B - 1e-9))
        S_bg = float(cs[n_urgent - 1]) if n_urgent > 0 else 0.0
        if not (B - K * XMIN < S_bg < B):
            return None
    urgent = rng.uniform(1.7, 2.3, n_urgent)
    tied = np.full(K, ELL_T)
    decoy = rng.uniform(80.0, 120.0, n - n_urgent - K)
    lax = np.concatenate([urgent, tied, decoy])
    xmax = np.concatenate([r_free[:n_urgent], np.full(K, r_T), r_free[n_urgent:]])
    perm = rng.permutation(n)
    return lax[perm], xmax[perm]


def value(x, A, Bc, C):
    return float(np.sum(A * (np.log(Bc * np.asarray(x) + C) - np.log(C))))


def run_cell(B, n, K, builder, instances):
    acc = {m: [] for m in METHODS}
    for s in range(REPS):
        built = builder(B, n, K, seed=s)
        if built is None:
            continue
        lax, xmax = built
        A, Bc, C = xmax.copy(), 1.0 / xmax, lax - 1.0

        with warnings.catch_warnings():
            warnings.simplefilter('ignore')
            x_star, _, _ = bic.run_MICP(B, A, Bc, C, XMIN, xmax, time_limit=MIP_TIME_LIMIT)
        v_star = value(x_star, A, Bc, C)
        if v_star <= 0:
            continue

        x_bic, _, _ = bic.run_BIC(B, EPS, A, Bc, C, XMIN, xmax)
        acc['BIC'].append(100.0 * value(x_bic, A, Bc, C) / v_star)
        for m in HEURISTICS:
            x_h, _ = bic.run_heuristic(m, B, EPS, A, Bc, C, XMIN, xmax)
            acc[m].append(100.0 * value(x_h, A, Bc, C) / v_star)
        instances.extend(dict(seed=s, method=m, ratio=acc[m][-1]) for m in METHODS)

    if not acc['BIC']:
        return None
    return {m: float(np.median(v)) for m, v in acc.items()}


def main():
    rows, instance_rows = [], []
    for scenario, builder in [('HB1_stress', build_h1), ('HB2_stress', build_h2)]:
        for pct in PCTS:
            K = int(round(pct / 100 * N))
            for rho in RHOS:
                B = rho * N * XMAX
                inst = []
                res = run_cell(B, N, K, builder, inst)
                instance_rows.extend(dict(scenario=scenario, pct=pct, rho=rho, **r)
                                     for r in inst)
                if res is None:
                    continue
                rows.append(dict(scenario=scenario, pct=pct, rho=rho,
                                 **{f'{m}_ratio': res[m] for m in METHODS}))
                print(scenario, pct, rho, {m: round(res[m], 2) for m in METHODS}, flush=True)

    pd.DataFrame(rows).to_csv('results/opt_cells.csv', index=False)
    pd.DataFrame(instance_rows).to_csv('results/opt_instances.csv', index=False)


if __name__ == '__main__':
    main()
