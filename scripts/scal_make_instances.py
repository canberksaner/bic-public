"""Fig. 2 instances: pairs at the same budget that differ in the laxity of one
EV. In the gap instance the budget lies inside an Everett jump; in the no-gap
instance it lies on the dual path.

Output: results/scal_instances.npz
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import bic
from bic.bic import calculate_lambda_th, calculate_x_lambda

XMIN = 4.16
XMAX = 11.0
RHO = 0.38
EPS = 1e-13
MIP_THREADS = 1
LAXITY_LO = 2.0
LAXITY_HI = 300.0
NS = [10, 20, 50, 100, 200, 500, 1000]
REPS = 5
PAIR_SEARCH = 100
PAIR_SEARCH_MAX = 1000
SEED_BASE = 260_000
NO_GAP_MARGIN = 1e-2
CASE_PATH = 'results/scal_instances.npz'


def draw_ratings(n, seed):
    rng = np.random.default_rng(10_000_000 + seed)
    return rng.choice(np.asarray(bic.RATINGS_KW), size=n)


def instance_arrays(laxity, xmax):
    xmax = np.asarray(xmax, dtype=float)
    return xmax.copy(), 1.0 / xmax, np.asarray(laxity, dtype=float) - 1.0


def allocation_at(multiplier, laxity, xmax):
    A, B, C = instance_arrays(laxity, xmax)
    thresholds = calculate_lambda_th(A, B, C, XMIN)
    return calculate_x_lambda(multiplier, A, B, C, 0, XMIN, A, thresholds)


def probe_fast_path(budget, laxity, xmax):
    """The fast-path bisection; returns the bracket when it fails."""
    A, B, C = instance_arrays(laxity, xmax)
    thresholds = calculate_lambda_th(A, B, C, XMIN)
    tolerance = max(1e-6, 1e-9 * budget)

    lower = 0.0
    upper = float(np.max(thresholds[np.isfinite(thresholds)]))
    while upper - lower > 1e-13:
        multiplier = 0.5 * (lower + upper)
        if multiplier == lower or multiplier == upper:
            break
        total = float(np.sum(calculate_x_lambda(
            multiplier, A, B, C, 0, XMIN, A, thresholds)))
        if 0.0 <= budget - total <= tolerance:
            return {'hit': True, 'lower': np.nan, 'upper': np.nan}
        if total > budget:
            lower = multiplier
        else:
            upper = multiplier
    return {'hit': False, 'lower': lower, 'upper': upper}


def close_gap_at(multiplier, laxity, budget, xmax):
    """Change the laxity of one EV so that the dual allocation meets the budget."""
    allocation = allocation_at(multiplier, laxity, xmax)
    residual = float(budget - np.sum(allocation))
    active = np.flatnonzero(allocation > 0)
    if not len(active):
        return None

    targets = allocation[active] + residual
    caps = xmax[active]
    valid = (targets >= XMIN - 1e-12) & (targets <= caps + 1e-12)
    if not np.any(valid):
        return None

    candidates = active[valid]
    targets = np.clip(targets[valid], XMIN, caps[valid])
    new_m = 1.0 / multiplier - targets / xmax[candidates]
    positive = new_m > 0
    candidates = candidates[positive]
    new_m = new_m[positive]
    if not len(candidates):
        return None

    deltas = np.abs(new_m + 1.0 - laxity[candidates])
    for position in np.argsort(deltas):
        ev = int(candidates[position])
        no_gap = laxity.copy()
        no_gap[ev] = new_m[position] + 1.0
        if probe_fast_path(budget, no_gap, xmax)['hit']:
            return no_gap, ev, float(deltas[position])
    return None


def build_pair(n, budget, seed_start):
    """The pair with the smallest laxity change over the searched seeds."""
    candidates = []
    search_stop = seed_start + PAIR_SEARCH
    seed = seed_start
    while seed < seed_start + PAIR_SEARCH_MAX:
        current_seed = seed
        seed += 1
        laxity = np.random.default_rng(current_seed).uniform(LAXITY_LO, LAXITY_HI, n)
        xmax = draw_ratings(n, current_seed)
        gap_probe = probe_fast_path(budget, laxity, xmax)
        if not gap_probe['hit']:
            for multiplier in (gap_probe['upper'] * (1.0 + NO_GAP_MARGIN),
                               gap_probe['lower'] * (1.0 - NO_GAP_MARGIN)):
                closed = close_gap_at(multiplier, laxity, budget, xmax)
                if closed is None:
                    continue
                no_gap, ev, delta = closed
                candidates.append((delta, current_seed, laxity, no_gap, ev, gap_probe, xmax))

        if seed >= search_stop:
            if candidates:
                break
            search_stop = min(search_stop + PAIR_SEARCH, seed_start + PAIR_SEARCH_MAX)

    if not candidates:
        raise RuntimeError(f'No pair for n={n}')
    delta, seed, gap, no_gap, ev, gap_probe, xmax = min(candidates, key=lambda c: c[0])

    total_above = float(np.sum(allocation_at(gap_probe['lower'], gap, xmax)))
    total_below = float(np.sum(allocation_at(gap_probe['upper'], gap, xmax)))
    assert total_below < budget < total_above
    assert total_above - total_below >= XMIN - 1e-5
    return dict(gap=gap, no_gap=no_gap, xmax=xmax, seed=seed, changed_ev=ev,
                laxity_delta=delta)


def main():
    cases = {
        'meta_xmin': np.array(XMIN),
        'meta_xmax': np.array(XMAX),
        'meta_rho': np.array(RHO),
        'meta_eps': np.array(EPS),
        'meta_mip_threads': np.array(MIP_THREADS),
        'meta_ns': np.asarray(NS),
    }
    for n in NS:
        budget = RHO * n * XMAX
        for rep in range(REPS):
            pair = build_pair(n, budget, SEED_BASE + 10_000 * rep + 101 * n)
            key = f'n{n}_r{rep}'
            cases[f'{key}_gap_laxity'] = pair['gap']
            cases[f'{key}_no_gap_laxity'] = pair['no_gap']
            cases[f'{key}_xmax'] = pair['xmax']
            cases[f'{key}_budget_kw'] = np.array(budget)
            cases[f'{key}_source_seed'] = np.array(pair['seed'])
            cases[f'{key}_changed_ev'] = np.array(pair['changed_ev'])
            cases[f'{key}_laxity_delta'] = np.array(pair['laxity_delta'])
            print(f'n={n} rep={rep} seed={pair["seed"]}', flush=True)
    np.savez_compressed(CASE_PATH, **cases)


if __name__ == '__main__':
    main()
