"""Fig. 1: worst cell over the share of tied EVs at each budget ratio.
Ratios above 100% (MIP stopped at its time limit) are shown as 100%."""
import os
import sys

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from bic.plotting import (COLOR, LABEL_PAD, LABEL_PT, LR_FIGSIZE, MARKER, METHODS, TITLE,
                          apply_style, figure_legend, save)

SCENARIOS = [('HB1_stress', 'HB1-adversarial'), ('HB2_stress', 'HB2-adversarial')]

apply_style()
df = pd.read_csv('results/opt_cells.csv')
fig, axes = plt.subplots(1, 2, figsize=LR_FIGSIZE, sharex=True, sharey=True)
for panel, (ax, (scenario, label)) in enumerate(zip(axes, SCENARIOS)):
    d = df[df.scenario == scenario]
    for m in METHODS:
        worst = d.assign(r=np.minimum(d[f'{m}_ratio'], 100.0)).groupby('rho').r.min()
        ax.plot(worst.index, worst.values, linewidth=1.2, markersize=3.0, label=m,
                color=COLOR[m], marker=MARKER[m])
    ax.set_title(f'({"ab"[panel]}) {label} instances', **TITLE)
    ax.set_xlabel(r'Budget ratio $\sigma$', fontsize=LABEL_PT, labelpad=LABEL_PAD)
    ax.grid(True, alpha=0.22, linewidth=0.4)
    ax.tick_params(labelsize=7)
axes[0].set_xticks([0.2, 0.4, 0.6, 0.8])
axes[0].set_ylim(-3, 104)
axes[0].set_yticks([0, 25, 50, 75, 100])
axes[0].set_ylabel('Optimality ratio [%]', fontsize=LABEL_PT, labelpad=LABEL_PAD)
axes[1].tick_params(labelleft=False)
fig.subplots_adjust(left=0.13, right=0.99, bottom=0.34, top=0.90, wspace=0.07)
handles, labels = axes[0].get_legend_handles_labels()
figure_legend(fig, handles, labels, axes)
save(fig, 'fig1_optimality')
