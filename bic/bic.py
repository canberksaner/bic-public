"""Bisect-Index-Choose (BIC) for utilities f_i(x) = A_i log(B_i x + C_i)."""
import itertools
import math
import time
import warnings
import numpy as np

# Every bisection stops when 0 <= budget - S(lambda) <= DELTA_REL * budget.
DELTA_REL = 1e-6


def _delta(budget):
    return DELTA_REL * budget


def calculate_lambda_th(A, B, C, xmin):
    """lambda_th[i] = (f_i(xmin) - f_i(0)) / xmin."""
    n = len(A)
    assert len(B) == n and len(C) == n
    assert xmin > 0 and np.all(A > 0) and np.all(B > 0)

    f_0 = np.full(n, -np.inf)
    idx0 = C > 0
    f_0[idx0] = A[idx0] * np.log(C[idx0])

    BxC = B * xmin + C
    f_min = np.full(n, -np.inf)
    idxm = BxC > 0
    f_min[idxm] = A[idxm] * np.log(BxC[idxm])

    lambda_th = (f_min - f_0) / xmin
    assert not np.any(np.isnan(lambda_th))
    return lambda_th


def calculate_x_lambda(lambda_val, A, B, C, status, xmin, xmax, lambda_th=None):
    """Allocation at lambda on {0} U [xmin, xmax] (status 0) or [xmin, xmax] (status 1)."""
    n = len(A)
    assert lambda_val > 0 and len(B) == n and len(C) == n
    assert np.all(A > 0) and np.all(B > 0) and status in (0, 1)
    assert xmin > 0 if status == 0 else xmin >= 0

    xmax = np.asarray(xmax, dtype=float)
    if xmax.ndim == 0:
        xmax = np.full(n, float(xmax))
    assert len(xmax) == n and np.all(xmax >= xmin)

    x_raw = (A / lambda_val) - (C / B)
    x_clip = np.minimum(xmax, np.maximum(xmin, x_raw))
    if status == 1:
        return x_clip

    if lambda_th is None:
        lambda_th = calculate_lambda_th(A, B, C, xmin)
    x = np.zeros(n)
    active = lambda_val < lambda_th
    x[active] = x_clip[active]
    return x


def bisection_phase(budget, eps, A, B, C, status, xmin, xmax, lambda_th=None,
                    tol=None):
    """Bisection on lambda for sum(x(lambda)) = budget.

    Returns (flag, x, lambda0, lambda1): flag 1 with the allocation x, or
    flag 0 with the bracket [lambda0, lambda1] of an Everett gap.
    """
    n = len(A)
    assert len(B) == n and len(C) == n
    assert np.all(A > 0) and np.all(B > 0) and np.all(C > 0) and status in (0, 1)
    assert xmin > 0 if status == 0 else xmin >= 0
    assert budget >= 0 and eps > 0
    if tol is None:
        tol = _delta(budget)

    xmax = np.asarray(xmax, dtype=float)
    if xmax.ndim == 0:
        xmax = np.full(n, float(xmax))
    assert len(xmax) == n and np.all(xmax >= xmin)

    if np.sum(xmax) <= budget:
        return 1, xmax.copy(), np.nan, np.nan

    lambda0 = 0.0
    if status == 0:
        if lambda_th is None:
            lambda_th = calculate_lambda_th(A, B, C, xmin)
        finite_th = lambda_th[np.isfinite(lambda_th)]
        assert len(finite_th) > 0
        L = np.max(finite_th)
        lambda_th_used = lambda_th
    else:
        ratios = (A * B) / C
        finite = np.isfinite(ratios)
        assert np.any(finite)
        L = np.max(ratios[finite])
        assert budget >= n * xmin - eps
        lambda_th_used = None

    lambda1 = L
    while (lambda1 - lambda0) > eps:
        lam = 0.5 * (lambda0 + lambda1)
        if lam == lambda0 or lam == lambda1:
            break
        x_mid = calculate_x_lambda(lam, A, B, C, status, xmin, xmax, lambda_th_used)
        s_mid = np.sum(x_mid)
        if 0.0 <= budget - s_mid <= tol:
            return 1, x_mid, np.nan, np.nan
        elif s_mid > budget:
            lambda0 = lam
        else:
            lambda1 = lam

    if status == 1:
        x_opt = calculate_x_lambda(lambda1, A, B, C, status, xmin, xmax, lambda_th_used)
        return 1, x_opt, np.nan, np.nan
    return 0, None, lambda0, lambda1


def dominance_order(A, B, C, xmin, xmax, check_chain=True):
    """Priority order: f_i'(0) descending, ties by f_i'(xmax) descending.

    For the log family, f_i' >= f_j' on [0, xmax] iff it holds at both ends,
    so chain_ok checks adjacent pairs at x = 0 and x = xmax.
    """
    xmax_hi = float(np.max(xmax))
    fp0 = A * B / C
    fpx = A * B / (B * xmax_hi + C)
    order = np.lexsort((-fpx, -fp0))

    chain_ok = True
    if check_chain:
        tol = 1e-12
        chain_ok = bool(
            np.all(np.diff(fp0[order]) <= tol)
            and np.all(np.diff(fpx[order]) <= tol))
    return order, chain_ok


def _restriction(budget, eps, A, B, C, xmin, xmax, idx):
    """Value and allocation of the convex problem on the on-set idx."""
    As, Bs, Cs, xs = A[idx], B[idx], C[idx], xmax[idx]
    if np.sum(xs) <= budget:
        x = xs.copy()
    else:
        CdB = Cs / Bs
        lam0, lam1 = 0.0, float(np.max(As * Bs / (Bs * xmin + Cs)))
        delta = _delta(budget)
        x = None
        while lam1 - lam0 > eps:
            lam = 0.5 * (lam0 + lam1)
            if lam == lam0 or lam == lam1:
                break
            x_mid = np.minimum(xs, np.maximum(xmin, As / lam - CdB))
            s = np.sum(x_mid)
            if 0.0 <= budget - s <= delta:
                x = x_mid
                break
            if s > budget:
                lam0 = lam
            else:
                lam1 = lam
        if x is None:
            x = np.minimum(xs, np.maximum(xmin, As / lam1 - CdB))
    return float(np.sum(As * (np.log(Bs * x + Cs) - np.log(Cs)))), x


def _choosing_phase(budget, eps, A, B, C, xmin, xmax, groups, c_max):
    """Best counts per rating group: binary search for one group, otherwise
    enumeration of all but the last two groups and Choose (Algorithm 1) on
    the last two. Returns the on-set and its allocation."""
    cache = {}

    def V(counts):
        if counts not in cache:
            idx = np.concatenate(
                [g[:k] for g, k in zip(groups, counts)]
                + [np.array([], int)]).astype(int)
            if len(idx) == 0:
                cache[counts] = (0.0, idx, np.zeros(0))
            else:
                v, x = _restriction(budget, eps, A, B, C, xmin, xmax, idx)
                cache[counts] = (v, idx, x)
        return cache[counts][0]

    if len(groups) == 1:
        lo, hi = 0, min(len(groups[0]), c_max)
        while lo < hi:
            mid = (lo + hi) // 2
            if V((mid + 1,)) > V((mid,)):
                lo = mid + 1
            else:
                hi = mid
        best = (lo,)
        V(best)
    else:
        best, V_best = None, -math.inf
        n_a, n_b = len(groups[-2]), len(groups[-1])
        for head in itertools.product(
                *[range(len(g) + 1) for g in groups[:-2]]):
            room = c_max - sum(head)
            if room < 0:
                continue
            t = min(n_b, room)
            for c_a in range(min(n_a, room) + 1):
                t = min(t, room - c_a)
                while t > 0 and V(head + (c_a, t - 1)) >= V(head + (c_a, t)):
                    t -= 1
                v = V(head + (c_a, t))
                if v > V_best:
                    V_best, best = v, head + (c_a, t)
    _, idx, x = cache[best]
    return idx, x


def run_BIC(budget, eps, A, B, C, xmin, xmax, fastpath=True):
    """Solve max sum_i f_i(x_i) s.t. sum_i x_i <= budget, x_i in {0} U [xmin, xmax_i].

    EVs with equal xmax form a rating group. fastpath=False skips the fast
    path. Returns (x, objective, seconds).
    """
    t0 = time.time()
    tol = 1e-6

    A = np.asarray(A, dtype=float)
    B = np.asarray(B, dtype=float)
    C = np.asarray(C, dtype=float)
    n = len(A)

    xmax = np.asarray(xmax, dtype=float)
    if xmax.ndim == 0:
        xmax = np.full(n, float(xmax))

    assert len(B) == n and len(C) == n
    assert np.all(A > 0) and np.all(B > 0) and np.all(C > 0)
    assert xmin > 0 and np.all(xmax >= xmin) and budget >= 0

    if np.sum(xmax) <= budget:
        x_star = xmax.copy()
        objval = np.sum(A * np.log(B * x_star + C))
        return x_star, objval, time.time() - t0

    # Bisect
    if fastpath:
        lambda_th = calculate_lambda_th(A, B, C, xmin)
        flag, x_fast, _, _ = bisection_phase(
            budget, eps, A, B, C, 0, xmin, xmax, lambda_th)
        if flag == 1:
            x_star = x_fast
            objval = np.sum(A * np.log(B * x_star + C))
            comptime = time.time() - t0
            ok = (np.abs(x_star) <= tol) | ((x_star >= xmin - tol) & (x_star <= xmax + tol))
            assert np.all(ok)
            assert np.sum(x_star) <= budget + tol
            return x_star, objval, comptime

    # Index
    caps = np.unique(xmax)
    groups = []
    for cap in caps:
        members = np.where(np.abs(xmax - cap) <= 1e-9)[0]
        g_order, chain_ok = dominance_order(
            A[members], B[members], C[members], xmin, xmax[members])
        if not chain_ok:
            warnings.warn('A rating group has no priority order; '
                          'the allocation may not be optimal.')
        groups.append(members[g_order])

    # Choose
    c_max = int(np.floor(budget / xmin + 1e-12))
    idx_best, x_best = _choosing_phase(
        budget, eps, A, B, C, xmin, xmax, groups, c_max)

    x_star = np.zeros(n)
    x_star[idx_best] = x_best
    objval = np.sum(A * np.log(B * x_star + C))
    comptime = time.time() - t0

    ok = (np.abs(x_star) <= tol) | ((x_star >= xmin - tol) & (x_star <= xmax + tol))
    assert np.all(ok)
    assert np.sum(x_star) <= budget + tol
    return x_star, objval, comptime
