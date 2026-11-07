"""Fig. 6 data. The normal budget of each day is B0 = 1.1 rho_star Bmax; from
13:00 to 14:00 it is cut by 0 to 100%. dr_sweep.csv holds the undelivered
energy per day and cut depth, dr_day.csv the power on 18 Jan 2024 with a
60% cut.

Usage: python scripts/dr_sweep.py [--workers W] [--n-days N]
Output: results/dr_sweep.csv, results/dr_day.csv
"""
import argparse
import datetime
import multiprocessing as mp
import os

import numpy as np
import pandas as pd

from common import METHODS, N_DAYS, load_day, rho_star, select_dates
import bic

KAPPA = 1.1
FRACS = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
CUT_HOUR, CUT_MIN = 13.0, 60
DAY, DAY_CUT = '2024-01-18', 0.6


def budget_fn(ev, n_peak, rs, cut):
    """B0 outside the cut window, B0 (1 - cut) inside."""
    B0 = KAPPA * rs * n_peak * max(bic.RATINGS_KW)
    t_start = int(round(CUT_HOUR * 60 - ev.anchor))
    t_end = t_start + CUT_MIN
    return B0, t_start, t_end, lambda t: B0 * (1.0 - cut) if t_start < t <= t_end else B0


def compute_day(job):
    date, rs = job
    ev, n_peak, _ = load_day(date)
    rows = []
    for f in FRACS:
        B0, _, _, budget = budget_fn(ev, n_peak, rs, f)
        res = bic.simulate(ev, budget, METHODS)
        for m in METHODS:
            rows.append(dict(date=date, method=m, frac=f, B_event_kw=B0 * (1.0 - f),
                             unmet_kwh=float(res[m][1].sum()),
                             total_req_kwh=float(ev.kwh_req.sum()),
                             n_evs=len(ev.arr), n_peak=n_peak))
    return rows


def single_day(rs):
    date = datetime.date.fromisoformat(DAY)
    ev, n_peak, _ = load_day(date)
    B0, t_start, t_end, budget = budget_fn(ev, n_peak, rs[date], DAY_CUT)
    T = int(ev.dep.max())
    df = pd.DataFrame({'hour': (ev.anchor + np.arange(T + 1)) / 60.0,
                       'budget_kw': [budget(t) for t in range(T + 1)]})
    res = bic.simulate(ev, budget, METHODS)
    for m in METHODS:
        df[m] = res[m][0]
        df[f'undelivered_{m}'] = res[m][1].sum()
    df = df.assign(date=DAY, kappa=KAPPA, cut=DAY_CUT, target_hour=CUT_HOUR,
                   dip_min=CUT_MIN, B0=B0, cut_start_h=df.hour.iloc[t_start],
                   cut_end_h=df.hour.iloc[t_end])
    df.to_csv('results/dr_day.csv', index=False)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=os.cpu_count())
    ap.add_argument('--n-days', type=int, default=N_DAYS)
    args = ap.parse_args()
    rs = rho_star()
    single_day(rs)
    jobs = [(d, rs[d]) for d in select_dates(args.n_days)]
    rows = []
    with mp.Pool(args.workers) as pool:
        for i, day_rows in enumerate(pool.imap_unordered(compute_day, jobs)):
            rows += day_rows
            print(f'[{i + 1}/{len(jobs)}] {day_rows[0]["date"]}', flush=True)
    pd.DataFrame(rows).sort_values(['date', 'method', 'frac']).to_csv(
        'results/dr_sweep.csv', index=False)


if __name__ == '__main__':
    main()
