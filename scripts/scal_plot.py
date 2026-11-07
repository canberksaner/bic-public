"""Fig. 2: median computation time per number of EVs."""
import os
import sys

import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from bic.plotting import apply_style, finish_runtime, runtime_axes, save

# label: (color, marker, linestyle, linewidth)
STYLE = {
    'BIC': ('#2a78d6', 's', '-', 1.6),
    'BIC without fast path': ('#2a78d6', 's', ':', 1.25),
    'MIP': ('#d62728', 'o', '-', 1.25),
}
SERIES = {'gap': ['BIC', 'MIP'], 'no_gap': ['BIC', 'BIC without fast path', 'MIP']}

data = pd.read_csv('results/scal_runtime.csv')
medians = data.groupby(['n', 'regime', 'configuration'], as_index=False)['time_s'].median()

apply_style(legend_frame=True)
fig, axes = runtime_axes()
lines = {}
for ax, regime in zip(axes, ['gap', 'no_gap']):
    for label in SERIES[regime]:
        sub = medians[(medians.regime == regime)
                      & (medians.configuration == label)].sort_values('n')
        color, marker, ls, lw = STYLE[label]
        lines[label], = ax.plot(sub.n, sub.time_s, color=color, marker=marker,
                                markersize=2.8, linestyle=ls, linewidth=lw)
finish_runtime(fig, axes, xs=medians.n.unique(), ylim=(1e-4, 1e1),
               yticks=[1e-4, 1e-3, 1e-2, 1e-1, 1e0, 1e1],
               handles=[lines[k] for k in STYLE],
               labels=['BIC', 'BIC w/o fast-path', 'MIP'])
save(fig, 'fig2_runtime')
