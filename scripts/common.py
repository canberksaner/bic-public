import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import bic

DATA = 'data/sessions_utrecht_filtered.csv'
TZ = 'Europe/Amsterdam'
XMIN = 4.16
N_DAYS = 714   # days with at least 10 EVs
METHODS = ['BIC', 'HB1', 'HB2']


def select_dates(n_days=N_DAYS):
    """The n_days days with the most sessions."""
    df = pd.read_csv(DATA)
    df['minutesAvailable'] = df['minutesAvailable'].round().astype(int)
    df['kWhRequested'] = np.minimum(df['kWhRequested'], df['minutesAvailable'] / 60.0 * 11.0)
    df = df[df['minutesAvailable'] / 60.0 - df['kWhRequested'] / 11.0 >= 0].copy()
    df['date_local'] = pd.to_datetime(
        df['connectionTime'], format='%a, %d %b %Y %H:%M:%S GMT', utc=True
    ).dt.tz_convert(TZ).dt.date
    return df.groupby('date_local').size().sort_values(ascending=False).index[:n_days].tolist()


def load_day(date):
    """Sessions of one day and its Bmax = n_peak * 22 kW."""
    ev = bic.EVInstance.from_csv(DATA, xmin=XMIN, days=[date], tz=TZ)
    n_peak = ev.n_peak
    return ev, n_peak, n_peak * max(bic.RATINGS_KW)


def rho_star():
    d = pd.read_csv('results/cap_rho_star.csv')
    return {pd.Timestamp(k).date(): float(v) for k, v in zip(d.date, d.rho_star)}
