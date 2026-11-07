"""Fig. 5 data: undelivered energy per day with a flat budget of 0.8 to 1.2
times rho_star, on the days of results/cap_rho_star.csv.

Usage: python scripts/cap_unserved.py [--workers W]
Output: results/cap_unserved.csv
"""
import argparse
import multiprocessing as mp
import os

import pandas as pd

from common import METHODS, load_day, rho_star
import bic

FACS = [0.8, 0.9, 1.0, 1.1, 1.2]


def compute_day(job):
    date, rs = job
    ev, n_peak, _ = load_day(date)
    rows = []
    for f in FACS:
        res = bic.simulate(ev, f * rs * n_peak * max(bic.RATINGS_KW), METHODS)
        for m in METHODS:
            rows.append(dict(date=date, fac=f, rho=f * rs, method=m,
                             unmet_kwh=float(res[m][1].sum()),
                             total_req_kwh=float(ev.kwh_req.sum()),
                             n_evs=len(ev.arr), n_peak=n_peak))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=os.cpu_count())
    args = ap.parse_args()
    jobs = list(rho_star().items())
    rows = []
    with mp.Pool(args.workers) as pool:
        for i, day_rows in enumerate(pool.imap_unordered(compute_day, jobs)):
            rows += day_rows
            print(f'[{i + 1}/{len(jobs)}] {day_rows[0]["date"]}', flush=True)
    pd.DataFrame(rows).sort_values(['date', 'fac', 'method']).to_csv(
        'results/cap_unserved.csv', index=False)


if __name__ == '__main__':
    main()
