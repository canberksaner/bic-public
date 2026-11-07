"""MIP reference (CVXPY + MOSEK) and the heuristics HB1 and HB2."""
import time

import numpy as np

from .bic import bisection_phase, dominance_order


def run_MICP(budget, A, B, C, xmin, xmax, verbose=False, threads=None,
             time_limit=None):
    """Mixed-integer convex program, solved by MOSEK with default settings.

    With time_limit [s], MOSEK's best integer-feasible allocation is returned
    when the limit is reached. Returns (x, objective, seconds).
    """
    import cvxpy as cp

    t0 = time.time()
    A = np.asarray(A, dtype=float)
    B = np.asarray(B, dtype=float)
    C = np.asarray(C, dtype=float)
    n = len(A)
    xmax = np.asarray(xmax, dtype=float)
    if xmax.ndim == 0:
        xmax = np.full(n, float(xmax))

    x = cp.Variable(n)
    z = cp.Variable(n, boolean=True)
    obj = cp.Maximize(cp.sum(cp.multiply(A, cp.log(cp.multiply(B, x) + C))))
    constraints = [
        x >= xmin * z,
        x <= cp.multiply(xmax, z),
        cp.sum(x) <= budget,
        x >= 0,
        x <= xmax,
    ]
    prob = cp.Problem(obj, constraints)

    mosek_params = {}
    if threads is not None:
        mosek_params['MSK_IPAR_NUM_THREADS'] = int(threads)
    if time_limit is not None:
        mosek_params['MSK_DPAR_OPTIMIZER_MAX_TIME'] = float(time_limit)
    solve_kw = {'mosek_params': mosek_params} if mosek_params else {}
    if time_limit is not None:
        solve_kw['accept_unknown'] = True
    prob.solve(solver=cp.MOSEK, verbose=verbose, **solve_kw)
    comptime = time.time() - t0

    run_MICP.last_status = prob.status
    run_MICP.last_capped = (time_limit is not None and comptime >= 0.98 * time_limit)
    if prob.status not in ('optimal', 'optimal_inaccurate') and not (
            time_limit is not None and x.value is not None):
        raise RuntimeError(f'Solver problem: {prob.status}')

    x_micp = x.value
    objval = float(np.sum(A * np.log(B * x_micp + C)))
    return x_micp, objval, comptime


def _solve_on_set(budget, eps, A, B, C, xmin, xmax, on):
    """Best allocation with the EVs in `on` in [xmin, xmax] and the rest at 0."""
    n = len(A)
    x = np.zeros(n)
    K = len(on)
    if K == 0:
        return x
    bud_top = budget - K * xmin
    if bud_top <= 0:
        x[on] = xmin
        return x
    flag, t_opt, _, _ = bisection_phase(
        bud_top, eps, A[on], B[on], C[on] + B[on] * xmin, 1, 0.0,
        xmax[on] - xmin)
    if flag != 1:
        raise RuntimeError('Bisection did not return a solution.')
    x[on] = xmin + t_opt
    return x


def run_heuristic(heuristic, budget, eps, A, B, C, xmin, xmax):
    """HB1: relax, switch off the EVs below xmin, re-solve.
    HB2: switch on the first floor(budget / xmin) EVs in priority order.

    Returns (x, objective).
    """
    A = np.asarray(A, dtype=float)
    B = np.asarray(B, dtype=float)
    C = np.asarray(C, dtype=float)
    n = len(A)
    xmax = np.asarray(xmax, dtype=float)
    if xmax.ndim == 0:
        xmax = np.full(n, float(xmax))
    heuristic = heuristic.upper()
    assert heuristic in ('HB1', 'HB2')

    order, _ = dominance_order(A, B, C, xmin, xmax, check_chain=False)
    if heuristic == 'HB2':
        k = min(n, int(np.floor(budget / xmin + 1e-12)))
        x_heur = _solve_on_set(budget, eps, A, B, C, xmin, xmax, order[:k])
    else:
        flag_relax, x_relax, _, _ = bisection_phase(
            budget, eps, A, B, C, 1, 0.0, xmax)
        if flag_relax != 1:
            raise RuntimeError('Relaxation did not return a solution.')
        on = np.where(x_relax >= xmin)[0]
        x_heur = _solve_on_set(budget, eps, A, B, C, xmin, xmax, on)

    assert np.all(x_heur >= -1e-9) and np.all(x_heur <= xmax + 1e-9)
    assert np.sum(x_heur) <= budget + 1e-6
    assert np.all((x_heur == 0) | (x_heur >= xmin - 1e-9))

    objval = float(np.sum(A * np.log(B * x_heur + C)))
    return x_heur, objval
