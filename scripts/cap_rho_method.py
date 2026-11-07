"""Fig. 4 data: the smallest flat budget rho^m (share of Bmax) at which each
method meets every request of the day, by bisection from [rho_star, 2 rho_star]
to a width of 0.1% of rho_star.

Usage: python scripts/cap_rho_method.py [--workers W] [--n-days N]
Output: results/cap_rho_method.csv
"""
import argparse
import multiprocessing as mp
import os

import numpy as np
import pandas as pd

from common import METHODS, N_DAYS, load_day, rho_star, select_dates
import bic

CROSS_TOL_REL = 1e-3
DONE_TOL = 1e-6


def find_crossing(ev, bmax, method, rs):
    def is_perfect(rho):
        _, rem = bic.simulate(ev, rho * bmax, [method])[method]
        return bool(np.all(rem <= DONE_TOL))

    tol = CROSS_TOL_REL * rs
    lo, hi = rs, 2.0 * rs
    while not is_perfect(hi):
        lo, hi = hi, 2.0 * hi
    if lo == rs and is_perfect(lo):
        lo = 0.0
    while hi - lo > tol:
        mid = round((lo + hi) / 2, 6)
        if is_perfect(mid):
            hi = mid
        else:
            lo = mid
    return hi


def compute_day(job):
    date, rs = job
    ev, n_peak, bmax = load_day(date)
    return [dict(date=date, method=m, n_evs=len(ev.arr), n_peak=n_peak,
                 rho_method=find_crossing(ev, bmax, m, rs)) for m in METHODS]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=os.cpu_count())
    ap.add_argument('--n-days', type=int, default=N_DAYS)
    args = ap.parse_args()
    rs = rho_star()
    jobs = [(d, rs[d]) for d in select_dates(args.n_days)]
    rows = []
    with mp.Pool(args.workers) as pool:
        for i, day_rows in enumerate(pool.imap_unordered(compute_day, jobs)):
            rows += day_rows
            print(f'[{i + 1}/{len(jobs)}] {day_rows[0]["date"]}', flush=True)
    pd.DataFrame(rows).sort_values(['date', 'method']).to_csv(
        'results/cap_rho_method.csv', index=False)


if __name__ == '__main__':
    main()
