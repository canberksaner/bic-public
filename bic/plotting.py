"""Figure style."""
import os

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import LogLocator, NullFormatter, ScalarFormatter
from matplotlib.transforms import Bbox

METHODS = ['BIC', 'HB1', 'HB2']
COLOR = {'BIC': '#2a78d6', 'HB1': '#eb6834', 'HB2': '#1b8f6a'}
MARKER = {'BIC': 's', 'HB1': 'o', 'HB2': '^'}

LR_FIGSIZE = (3.5, 1.6)
LR_TITLES = ['With an Everett gap', 'Without an Everett gap']
TICK_PT, LABEL_PT, LABEL_PAD = 7.0, 7.5, 1.5
TITLE = dict(fontsize=7, pad=2.5)

LEGEND_STYLE = dict(
    fontsize=6.0, handlelength=3.0, handletextpad=0.5, labelspacing=0.5,
    columnspacing=0.9, borderpad=0.4, borderaxespad=0.0, frameon=True,
    fancybox=False, shadow=False, framealpha=1.0, edgecolor='#aaaaaa',
    facecolor='#ffffff')


def apply_style(legend_frame=False):
    matplotlib.rcParams.update({
        'font.size': 8,
        'font.family': 'serif',
        'font.serif': ['cmr10'],
        'mathtext.fontset': 'cm',
        'axes.formatter.use_mathtext': True,
        'axes.linewidth': 0.5,
        'axes.unicode_minus': False,
        'lines.linewidth': 1.0,
        'xtick.direction': 'in',
        'ytick.direction': 'in',
        'xtick.top': True,
        'ytick.right': True,
        'xtick.major.size': 3,
        'ytick.major.size': 3,
        'xtick.major.width': 0.5,
        'ytick.major.width': 0.5,
        'legend.frameon': legend_frame,
        'text.usetex': False,
        'savefig.bbox': 'tight',
        'savefig.pad_inches': 0.05,
    })


def runtime_axes():
    """Two log-log panels side by side with a shared y-axis."""
    fig, axes = plt.subplots(1, 2, figsize=LR_FIGSIZE, sharex=True, sharey=True)
    for ax in axes:
        ax.set_xscale('log')
        ax.set_yscale('log')
        ax.grid(True, which='both', alpha=0.22, linewidth=0.4)
        ax.tick_params(labelsize=7)
    return fig, axes


def finish_runtime(fig, axes, xs, ylim, yticks, handles, labels):
    xs = sorted(xs)
    for panel, (ax, title) in enumerate(zip(axes, LR_TITLES)):
        ax.set_title(f'({"ab"[panel]}) {title}', **TITLE)
        ax.set_xticks([t for t in (10, 100, 1000) if xs[0] <= t <= xs[-1]])
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.set_xlim(xs[0] * 0.8, xs[-1] * 1.25)
        ax.set_xlabel('Number of EVs $n$', fontsize=LABEL_PT, labelpad=LABEL_PAD)
    axes[0].set_ylim(*ylim)
    axes[0].set_yticks(yticks)
    axes[0].yaxis.set_minor_locator(LogLocator(base=10, subs=(1.0,), numticks=20))
    axes[0].yaxis.set_minor_formatter(NullFormatter())
    axes[0].set_ylabel('Computation time [s]', fontsize=LABEL_PT, labelpad=LABEL_PAD)
    axes[1].tick_params(labelleft=False)
    fig.subplots_adjust(left=0.13, right=0.99, bottom=0.34, top=0.90, wspace=0.07)
    figure_legend(fig, handles, labels, axes)


def figure_legend(fig, handles, labels, axes, gap_in=0.08):
    """One-row legend below the axes; the margins are then fitted so that the
    figure keeps its size."""
    edge_in = float(matplotlib.rcParams['savefig.pad_inches'])
    legend = fig.legend(handles, labels, loc='upper center', bbox_to_anchor=(0.5, 0.5),
                        bbox_transform=fig.transFigure, ncol=len(handles), **LEGEND_STYLE)
    legend.get_frame().set_linewidth(0.45)
    W, H = fig.get_size_inches()

    def place(renderer):
        boxes = Bbox.union([ax.get_position() for ax in axes])
        deco = Bbox.union([ax.get_tightbbox(renderer) for ax in axes])
        deco = deco.transformed(fig.transFigure.inverted())
        anchor = (0.5 * (boxes.x0 + boxes.x1), deco.y0 - gap_in / H)
        legend.set_bbox_to_anchor(anchor, transform=fig.transFigure)

    for _ in range(6):
        fig.canvas.draw()
        renderer = fig.canvas.get_renderer()
        place(renderer)
        fig.canvas.draw()
        tight = fig.get_tightbbox(renderer)
        sp = fig.subplotpars
        ex, ey = edge_in / W, edge_in / H
        moves = dict(left=ex - tight.x0 / W, right=(1 - ex) - tight.x1 / W,
                     bottom=ey - tight.y0 / H, top=(1 - ey) - tight.y1 / H)
        if max(abs(v) for v in moves.values()) < 2e-4:
            break
        fig.subplots_adjust(**{k: getattr(sp, k) + v for k, v in moves.items()})
    fig.canvas.draw()
    place(fig.canvas.get_renderer())
    return legend


def draw_strips(ax, df, key, levels, ylim, tick_fmt, label_y=0.85):
    """Dots, box and whiskers (quartiles, 1.5 IQR) per method and level, with
    the mean undelivered energy of HB1 and HB2 above that of BIC [kWh]."""
    mean = df.groupby([key, 'method']).unmet_kwh.mean().unstack()
    rng = np.random.default_rng(0)
    width = 0.26
    for i, lv in enumerate(levels):
        for k, m in enumerate(METHODS):
            v = df[(df[key] == lv) & (df.method == m)].unmet_kwh.values
            x = i + (k - 1) * width
            ax.scatter(x + rng.uniform(-0.07, 0.07, len(v)), v, s=1.6, color=COLOR[m],
                       marker=MARKER[m], alpha=0.35, linewidth=0, zorder=2)
            ax.boxplot([v], positions=[x], widths=0.2, showfliers=False, patch_artist=True,
                       zorder=3, boxprops=dict(facecolor='none', edgecolor='#222222', lw=0.6),
                       medianprops=dict(color='#222222', lw=1.0),
                       whiskerprops=dict(lw=0.6, color='#222222'),
                       capprops=dict(lw=0.6, color='#222222'))
            if m != 'BIC':
                d = mean.loc[lv, m] - mean.loc[lv, 'BIC']
                ax.text(x, ylim * label_y, f'{d:+.0f}', ha='center', va='center',
                        fontsize=5.2, color='#222222', rotation=90,
                        bbox=dict(facecolor='white', edgecolor='none', pad=0.6))
    for i in range(len(levels) - 1):
        ax.axvline(i + 0.5, color='#dddddd', lw=0.5, zorder=0)
    ax.set_xticks(range(len(levels)))
    ax.set_xticklabels([tick_fmt(lv) for lv in levels])
    ax.set_xlim(-0.5, len(levels) - 0.5)
    ax.set_ylim(-0.02 * ylim, ylim)
    ax.grid(True, axis='y', alpha=0.22, lw=0.4)
    ax.tick_params(labelsize=TICK_PT)


def save(fig, name):
    os.makedirs('figures', exist_ok=True)
    fig.savefig(f'figures/{name}.pdf', bbox_inches='tight')
    plt.close(fig)
    print(f'figures/{name}.pdf')
