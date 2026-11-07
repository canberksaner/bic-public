"""Fig. 3: median time on the Pico, over WiFi, and on the PC."""
import os
import sys

import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from bic.plotting import apply_style, finish_runtime, runtime_axes, save

LINES = [
    ('t_chip_min_s', 'pico', 'Microctrl. (Cortex-M33)',
     dict(color='#2a78d6', marker='s', linestyle='-', linewidth=1.6)),
    ('round_trip_s', 'pico', 'Microctrl. + Wi-Fi',
     dict(color='#2a78d6', marker='s', linestyle=(0, (2.4, 1.2)), linewidth=1.25,
          markerfacecolor='white')),
    ('t_pc_min_s', 'pc', 'PC (Core i7)',
     dict(color='#7b3fbf', marker='o', linestyle='-', linewidth=1.25)),
]

sources = {
    'pico': pd.read_csv('results/pico_wifi.csv').groupby(['n', 'regime'], as_index=False)[
        ['t_chip_min_s', 'round_trip_s']].median(),
    'pc': pd.read_csv('results/pico_pc.csv').groupby(['n', 'regime'], as_index=False)[
        ['t_pc_min_s']].median(),
}

apply_style(legend_frame=True)
fig, axes = runtime_axes()
for ax, regime in zip(axes, ['gap', 'no_gap']):
    for column, source, label, style in LINES:
        sub = sources[source]
        sub = sub[sub.regime == regime].sort_values('n')
        ax.plot(sub.n, sub[column], markersize=2.8, label=label, **style)
handles, labels = axes[0].get_legend_handles_labels()
finish_runtime(fig, axes, xs=sorted(sources['pico'].n.unique()), ylim=(1e-7, 1e2),
               yticks=[1e-6, 1e-4, 1e-2, 1e0], handles=handles, labels=labels)
save(fig, 'fig3_microcontroller')
