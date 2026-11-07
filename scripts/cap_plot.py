"""Figs. 4 and 5."""
import os
import sys

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.ticker

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from bic.plotting import (COLOR, LABEL_PAD, LABEL_PT, MARKER, METHODS, TICK_PT, TITLE,
                          apply_style, draw_strips, figure_legend, save)

LAB = dict(fontsize=LABEL_PT, labelpad=LABEL_PAD)

apply_style()
handles = [plt.Line2D([0], [0], color=COLOR[m], marker=MARKER[m], lw=1.3, ms=4.5,
                      mec='white', mew=0.5, label=m) for m in METHODS]

# Fig. 4: share of days fully served against the capacity above rho_star
p = pd.read_csv('results/cap_rho_method.csv').pivot(
    index='date', columns='method', values='rho_method')
p = p.join(pd.read_csv('results/cap_rho_star.csv').set_index('date')[['rho_star']])
overhead = {m: 100.0 * (p[m] - p.rho_star) / p.rho_star for m in METHODS}

fig, ax = plt.subplots(figsize=(3.5, 1.615))
xmin = 0.05
xmax = 10 ** np.ceil(np.log10(max(o.max() for o in overhead.values())))
grid = np.logspace(np.log10(xmin), np.log10(xmax), 1201)
for m in METHODS:
    o = overhead[m].values
    ax.plot(grid, [100 * np.mean(o <= g) for g in grid], color=COLOR[m], lw=1.3, zorder=3)
    ax.plot(np.median(o), 50, marker=MARKER[m], color=COLOR[m], ms=4.5,
            mec='white', mew=0.5, ls='', zorder=4)
ax.set_xscale('log')
ax.set_xlim(xmin, xmax)
ax.xaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f'{v:g}'))
ax.set_ylim(0, 102)
ax.set_yticks([0, 25, 50, 75, 100])
ax.grid(True, alpha=0.22, lw=0.4)
ax.tick_params(labelsize=TICK_PT)
ax.set_xlabel(r'Capacity above $\rho^\star$ [%]', **LAB)
ax.set_ylabel('Days fully served [%]', **LAB)
ax.set_title('(a)', alpha=0.0, **TITLE)   # same top margin as the two-panel figures
figure_legend(fig, handles, METHODS, [ax])
save(fig, 'fig4_capacity')

# Fig. 5: undelivered energy per day
df = pd.read_csv('results/cap_unserved.csv')
fig, axes = plt.subplots(1, 2, figsize=(3.5, 1.63), gridspec_kw={'width_ratios': [2.0, 3.0]})
lo, hi = [0.8, 0.9], [1.0, 1.1, 1.2]
draw_strips(axes[0], df, 'fac', lo, 1.3 * df[df.fac.isin(lo)].unmet_kwh.max(),
            lambda v: f'{v:.1f}')
draw_strips(axes[1], df, 'fac', hi, 1.3 * df[df.fac.isin(hi)].unmet_kwh.quantile(0.995),
            lambda v: f'{v:.1f}')
for ax in axes:
    ax.set_xlabel(r'$\rho/\rho^\star$', **LAB)
axes[0].set_ylabel('Undelivered [kWh/day]', **LAB)
axes[0].set_title(r'(a) Below $\rho^\star$', **TITLE)
axes[1].set_title(r'(b) At and above $\rho^\star$ (zoomed)', **TITLE)
fig.subplots_adjust(wspace=0.32)
figure_legend(fig, handles, METHODS, list(axes))
save(fig, 'fig5_undelivered')
