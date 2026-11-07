"""Fig. 6."""
import datetime
import os
import sys

import pandas as pd
import matplotlib.pyplot as plt

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from bic.plotting import (COLOR, LABEL_PAD, LABEL_PT, METHODS, TICK_PT, TITLE,
                          apply_style, draw_strips, figure_legend, save)

LEVELS = [0.2, 0.6, 1.0]
BUDGET_COLOR = '#222222'
BUDGET_LS = (0, (3, 1.5))
CUT_COLOR = '#e9695a'
LAB = dict(fontsize=LABEL_PT, labelpad=LABEL_PAD)

day = pd.read_csv('results/dr_day.csv')
sweep = pd.read_csv('results/dr_sweep.csv')
levels = [lv for lv in sorted(sweep.frac.unique()) if any(abs(lv - x) < 1e-9 for x in LEVELS)]
sweep = sweep[sweep.frac.isin(levels)]

apply_style()
fig, (ax_a, ax_b) = plt.subplots(1, 2, figsize=(3.5, 1.61))

# (a) one day
h = day.hour.values
B0 = float(day.B0.iloc[0])
cut = int(round(100 * day.cut.iloc[0]))
c0, c1 = float(day.cut_start_h.iloc[0]), float(day.cut_end_h.iloc[0])
ax_a.axvspan(c0, c1, color=CUT_COLOR, alpha=0.15, lw=0)
for m in reversed(METHODS):
    ax_a.plot(h, day[m], color=COLOR[m], ls='-', lw=0.9)
ax_a.plot(h, day.budget_kw, color=BUDGET_COLOR, lw=0.9, ls=BUDGET_LS, drawstyle='steps-post')
ax_a.set_xlim(h[0], h[-1])
ax_a.set_xticks([t for t in range(0, 25, 4) if h[0] <= t <= h[-1]])
ax_a.set_ylim(0, 1.25 * B0)
ax_a.text(0.5 * (c0 + c1), 1.12 * B0, f'{cut}% cut', ha='center', va='center', fontsize=6)
ax_a.grid(True, alpha=0.22, lw=0.4)
ax_a.set_xlabel('Time of day [h]', **LAB)
ax_a.set_ylabel('Power [kW]', **LAB)
d = datetime.date.fromisoformat(day.date.iloc[0])
ax_a.set_title(f'(a) {d.day} {d:%b} {d.year}, {cut}% cut', **TITLE)

# (b) all days
draw_strips(ax_b, sweep, 'frac', levels, 1.25 * sweep.unmet_kwh.max(),
            lambda v: f'{int(round(100 * v))}%')
ax_b.set_xlabel('Cut depth', **LAB)
ax_b.set_ylabel('Undelivered [kWh/day]', **LAB)
ax_b.set_title(f'(b) All {sweep.date.nunique()} days', **TITLE)
ax_a.tick_params(labelsize=TICK_PT)

handles = [plt.Line2D([0], [0], color=BUDGET_COLOR, lw=1.2, ls=BUDGET_LS)]
handles += [plt.Line2D([0], [0], color=COLOR[m], ls='-', lw=1.2) for m in METHODS]
fig.subplots_adjust(wspace=0.42)
figure_legend(fig, handles, [r'Budget $B_t$'] + METHODS, [ax_a, ax_b])
save(fig, 'fig6_demand_response')
