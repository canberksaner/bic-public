"""Online simulation of a charging station over one day, one period per minute."""
from dataclasses import dataclass

import numpy as np
import pandas as pd

from .bic import run_BIC
from .benchmarks import run_heuristic

EPS = 1e-13
RATINGS_KW = (11.0, 22.0)
SESSION_SEED = 2026


def session_ratings(n_rows):
    """Rating of each row of the session CSV, 11 or 22 kW with equal probability."""
    rng = np.random.default_rng(SESSION_SEED)
    return rng.choice(np.asarray(RATINGS_KW), size=n_rows)


@dataclass
class EVInstance:
    arr: np.ndarray       # arrival [min after anchor, from 1]
    duration: np.ndarray  # parking time [min]
    kwh_req: np.ndarray   # requested energy [kWh]
    xmax: np.ndarray      # maximum rate [kW]
    xmin: float           # minimum rate [kW]
    anchor: int           # earliest arrival [min after midnight]

    @property
    def dep(self):
        return self.arr + self.duration

    @property
    def n_peak(self):
        T = int(self.dep.max())
        return max(int(((self.arr <= t) & (t < self.dep)).sum()) for t in range(1, T + 1))

    @classmethod
    def from_csv(cls, path, xmin, days, tz='Europe/Amsterdam'):
        """Sessions arriving on the given local dates."""
        df = pd.read_csv(path)
        df['xmax_kw'] = session_ratings(len(df))
        df['minutesAvailable'] = df['minutesAvailable'].round().astype(int)
        # Requests above what the charger can deliver are capped.
        max_deliverable_kwh = df['minutesAvailable'] / 60.0 * df['xmax_kw']
        df['kWhRequested'] = np.minimum(df['kWhRequested'], max_deliverable_kwh)
        df['laxity_h'] = df['minutesAvailable'] / 60.0 - df['kWhRequested'] / df['xmax_kw']
        df = df[df['laxity_h'] >= 0.0].copy()

        t = pd.to_datetime(df['connectionTime'], format='%a, %d %b %Y %H:%M:%S GMT',
                           utc=True).dt.tz_convert(tz)
        df['date_local'] = t.dt.date
        df['msm'] = t.dt.hour * 60 + t.dt.minute

        ev = df[df['date_local'].isin(list(days))].copy().reset_index(drop=True)
        anchor = int(ev['msm'].min())
        ev['arr'] = (ev['msm'] - anchor + 1).astype(int)
        return cls(
            arr=ev['arr'].values,
            duration=ev['minutesAvailable'].values.astype(int),
            kwh_req=ev['kWhRequested'].values,
            xmax=ev['xmax_kw'].values,
            xmin=float(xmin),
            anchor=anchor,
        )


def _schedule(method, budget, A, B, C, xmin, xmax):
    if method == 'BIC':
        x, _, _ = run_BIC(budget, EPS, A, B, C, xmin, xmax)
    else:
        x, _ = run_heuristic(method, budget, EPS, A, B, C, xmin, xmax)
    return x


def _simulate_one(ev, budget, method):
    T = int(ev.dep.max())
    arr, dep = ev.arr, ev.dep
    rem = ev.kwh_req.copy()
    power = np.zeros(T + 1)

    for t in range(1, T + 1):
        b_t = float(budget(t)) if callable(budget) else float(budget)
        active = np.where((arr <= t) & (t < dep) & (rem > 1e-6))[0]
        if not len(active):
            continue
        xmax_i = ev.xmax[active]
        e_i = rem[active]
        # sLLF utility: A log(B x + C) with laxity C + 1 in minutes
        A = xmax_i
        Bv = 1.0 / xmax_i
        C = np.maximum((dep[active] - t) - 60.0 * e_i / xmax_i - 1.0, 1e-6)

        x = _schedule(method, b_t, A, Bv, C, ev.xmin, xmax_i)
        xd = np.minimum(x, e_i * 60.0)
        rem[active] -= xd / 60.0
        rem = np.maximum(rem, 0.0)
        power[t] = xd.sum()
    return power, rem


def simulate(ev, budget, methods):
    """Simulate the day with a constant budget [kW] or a function budget(t).

    Returns {method: (power per minute [kW], remaining energy per EV [kWh])}.
    """
    return {m: _simulate_one(ev, budget, m) for m in methods}
