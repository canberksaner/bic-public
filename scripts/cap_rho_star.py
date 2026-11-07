"""Offline minimum capacity of each day: the smallest flat budget, as a share
rho_star of Bmax, at which all requests can be met with full knowledge of the
day (LP without the minimum rate, HiGHS).

Usage: python scripts/cap_rho_star.py [--workers W] [--n-days N]
Output: results/cap_rho_star.csv
"""
import argparse
import multiprocessing as mp
import os

import numpy as np
import pandas as pd
import scipy.sparse as sp
from scipy.optimize import linprog

from common import N_DAYS, load_day, select_dates


def min_flat_budget(ev):
    idx_i, idx_t = [], []
    for i in range(len(ev.arr)):
        ts = np.arange(int(ev.arr[i]), int(ev.dep[i]))
        idx_i.extend([i] * len(ts))
        idx_t.extend(ts)
    idx_i = np.asarray(idx_i)
    idx_t = np.asarray(idx_t)
    nv = len(idx_i)

    # energy: -sum_t x_it / 60 <= -E_i
    A_energy = sp.csr_matrix((-np.ones(nv) / 60.0, (idx_i, np.arange(nv))),
                             shape=(len(ev.arr), nv + 1))
    # budget: sum_i x_it - B <= 0
    slots, pos = np.unique(idx_t, return_inverse=True)
    rows = np.concatenate([pos, np.arange(len(slots))])
    cols = np.concatenate([np.arange(nv), np.full(len(slots), nv)])
    vals = np.concatenate([np.ones(nv), -np.ones(len(slots))])
    A_budget = sp.csr_matrix((vals, (rows, cols)), shape=(len(slots), nv + 1))

    A = sp.vstack([A_energy, A_budget]).tocsr()
    b = np.concatenate([-ev.kwh_req, np.zeros(len(slots))])
    c = np.zeros(nv + 1)
    c[-1] = 1.0
    res = linprog(c, A_ub=A, b_ub=b,
                  bounds=[(0.0, float(ev.xmax[i])) for i in idx_i] + [(0.0, None)],
                  method='highs')
    if res.status != 0:
        raise RuntimeError(res.message)
    return float(res.x[-1])


def compute_day(date):
    ev, n_peak, bmax = load_day(date)
    B_star = min_flat_budget(ev)
    return dict(date=date, rho_star=B_star / bmax, B_star_kw=B_star,
                n_evs=len(ev.arr), n_peak=n_peak)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=os.cpu_count())
    ap.add_argument('--n-days', type=int, default=N_DAYS)
    args = ap.parse_args()
    with mp.Pool(args.workers) as pool:
        rows = pool.map(compute_day, select_dates(args.n_days))
    pd.DataFrame(rows).sort_values('date').to_csv('results/cap_rho_star.csv', index=False)


if __name__ == '__main__':
    main()
