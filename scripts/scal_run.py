"""Fig. 2 data: computation time of BIC (with and without the fast path) and
of the MIP (MOSEK, one thread) on the instance pairs.

Output: results/scal_runtime.csv
"""
import os
import sys
import time
import warnings

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
import bic
from scal_make_instances import CASE_PATH, EPS, MIP_THREADS, instance_arrays

CSV_PATH = 'results/scal_runtime.csv'
# (label, fastpath) of the BIC runs per regime
CONFIGS = {
    'gap': (('BIC', True),),
    'no_gap': (('BIC', True), ('BIC without fast path', False)),
}


def solve_bic(budget, laxity, xmin, xmax, fastpath):
    A, B, C = instance_arrays(laxity, xmax)
    start = time.perf_counter()
    x, value, _ = bic.run_BIC(budget, EPS, A, B, C, xmin, xmax, fastpath=fastpath)
    elapsed = time.perf_counter() - start
    return {
        'time_s': elapsed,
        'objective': value,
        'allocated_kw': float(np.sum(x)),
        'active_evs': int(np.count_nonzero(x > 1e-6)),
        'budget_residual_kw': float(budget - np.sum(x)),
    }


def solve_mip(budget, laxity, xmin, xmax):
    A, B, C = instance_arrays(laxity, xmax)
    start = time.perf_counter()
    _, value, _ = bic.run_MICP(budget, A, B, C, xmin, A, threads=MIP_THREADS)
    return {'time_s': time.perf_counter() - start, 'objective': value}


def main():
    archive = np.load(CASE_PATH)
    xmin = float(archive['meta_xmin'])
    rho = float(archive['meta_rho'])
    warnings.filterwarnings('ignore', module='mosek')

    # warm-up: imports, licence check, caches
    lax, budget, xmax = (archive['n10_r0_gap_laxity'], float(archive['n10_r0_budget_kw']),
                         np.asarray(archive['n10_r0_xmax'], dtype=float))
    for _, fastpath in CONFIGS['gap'] + CONFIGS['no_gap']:
        solve_bic(budget, lax, xmin, xmax, fastpath)
    solve_mip(budget, lax, xmin, xmax)

    records = []
    for n in [int(v) for v in archive['meta_ns']]:
        reps = sorted(int(k[len(f'n{n}_r'):-len('_budget_kw')]) for k in archive.files
                      if k.startswith(f'n{n}_r') and k.endswith('_budget_kw'))
        for rep in reps:
            key = f'n{n}_r{rep}'
            budget = float(archive[f'{key}_budget_kw'])
            xmax = np.asarray(archive[f'{key}_xmax'], dtype=float)
            common = dict(n=n, rep=rep, source_seed=int(archive[f'{key}_source_seed']),
                          budget_kw=budget, rho=rho)
            for regime in ('gap', 'no_gap'):
                laxity = archive[f'{key}_{regime}_laxity']
                configurations = list(CONFIGS[regime])
                if rep % 2:
                    configurations.reverse()
                results = {}
                for label, fastpath in configurations:
                    results[label] = solve_bic(budget, laxity, xmin, xmax, fastpath)
                    records.append(dict(common, regime=regime, configuration=label,
                                        fastpath=int(fastpath), **results[label]))
                mip = solve_mip(budget, laxity, xmin, xmax)
                records.append(dict(common, regime=regime, configuration='MIP',
                                    fastpath=np.nan, **mip))
                for record in records[-(len(configurations) + 1):]:
                    record['objective_difference_from_bic'] = (
                        record['objective'] - results['BIC']['objective'])
                print(f'n={n:5d} rep={rep} {regime:6s}: BIC {1e3 * results["BIC"]["time_s"]:.3f} ms, '
                      f'MIP {mip["time_s"]:.3f} s', flush=True)

    cols = ['n', 'regime', 'rep', 'source_seed', 'budget_kw', 'rho', 'configuration',
            'fastpath', 'time_s', 'objective', 'allocated_kw', 'active_evs',
            'budget_residual_kw', 'objective_difference_from_bic']
    pd.DataFrame(records).reindex(columns=cols).to_csv(CSV_PATH, index=False)


if __name__ == '__main__':
    main()
