# Bisect-Index-Choose (BIC)

Code and data for the paper

> C. B. Saner, "Bisect-Index-Choose: A Fast and Exact Algorithm for EV Charging under Minimum Charging Rates."

BIC allocates a power budget among the EVs connected to a charging station. Each EV charges either at zero or at a rate between a common minimum and its own maximum. BIC finds the allocation that maximizes a sum of concave utilities without a solver. The Python implementation is in `bic/bic.py`, and a C implementation for microcontrollers is in `firmware/bic_core.c`.

**Contents:** [Setup](#setup) · [Reproducing the figures](#reproducing-the-figures) · [Using BIC](#using-bic) · [Proofs in Lean](#proofs-in-lean) · [Files](#files) · [Data](#data)

## Setup

Python 3.13 and the packages in `requirements.txt`:

```bash
pip install -r requirements.txt
```

Figs. 1 and 2 compare BIC with a mixed-integer program solved by MOSEK, which needs a licence (free for academic use, [mosek.com](https://www.mosek.com)). Fig. 3 needs a Raspberry Pi Pico 2 W (see [Fig. 3](#fig-3-microcontroller)).

Run every command from the repository root. First build the session file that Figs. 4 to 6 read:

```bash
python scripts/prep_sessions.py
```

## Reproducing the figures

Each figure has one or more run scripts, which write their results to `results/`, and one plot script, which reads `results/` and writes the figure to `figures/`. The results of the paper are included, so the plot scripts alone redraw the figures of the paper in a few seconds.

The times below were measured on a laptop with an Intel Core i7-10750H (6 cores). Scripts with `--workers` use all cores by default. All run scripts together take about 4 hours, and each plot script a few seconds.

| Figure | Commands | Time |
|---|---|---|
| 1. Optimality | `python scripts/opt_run.py`<br>`python scripts/opt_plot.py` | 2.5 min<br> |
| 2. Computation time | `python scripts/scal_make_instances.py`<br>`python scripts/scal_run.py`<br>`python scripts/scal_plot.py` | 10 s<br>1 min<br> |
| 3. Microcontroller | see [Fig. 3](#fig-3-microcontroller) | |
| 4. Capacity needed | `python scripts/cap_rho_star.py`<br>`python scripts/cap_rho_method.py`<br>`python scripts/cap_plot.py` | 7 min<br>1 h 50 min<br> |
| 5. Undelivered energy | `python scripts/cap_unserved.py`<br>`python scripts/cap_plot.py` | 55 min<br> |
| 6. Demand response | `python scripts/dr_sweep.py`<br>`python scripts/dr_plot.py` | 1 h<br> |

`cap_rho_star.py` must run before `cap_rho_method.py`, `cap_unserved.py` and `dr_sweep.py`, which read its offline minimum capacity of each day. For a quick check, `cap_rho_star.py`, `cap_rho_method.py` and `dr_sweep.py` take `--n-days N` to run on the N busiest days only, and `cap_unserved.py` then runs on the same days. Every run replaces its files in `results/`.

The share of EVs rated 11 or 22 kW quoted in Sec. II comes from

```bash
python scripts/openev_share.py
```

All random draws are seeded, so the instances and results are the same on every run. The computation times of Figs. 2 and 3 depend on the machine. In Fig. 1, MOSEK stops after 10 s per instance, so where it reaches this limit its value can depend on the machine and its load.

### Fig. 3: microcontroller

The firmware in `firmware/` runs BIC on a Raspberry Pi Pico 2 W and answers requests over WiFi (TCP port 4242). The scripts below run on Windows.

<details>
<summary>Build, load and run</summary>

1. Open `firmware/` in VS Code with the Raspberry Pi Pico extension, which installs the Pico SDK 2.3.1 and the build tools into `~/.pico-sdk`.
2. Copy `firmware/wifi_credentials.h.example` to `firmware/wifi_credentials.h` and enter a 2.4 GHz network that the PC is also on.
3. Connect the Pico over USB and load the firmware:

```bash
python scripts/pico_flash.py setup
```

Once its LED shows a heartbeat, the Pico is on the network. Then:

```bash
python scripts/pico_run.py       # on the Pico, over WiFi (1 min)
pip install ziglang
python scripts/pico_run_pc.py    # the same C code on the PC (30 s, a few minutes for the first compile)
python scripts/pico_plot.py
```

`pico_run.py` finds the Pico by scanning the local network. If the scan fails, pass the address that the Pico prints over USB serial with `--host <ip>`. Later firmware builds can be loaded over WiFi with `python scripts/pico_flash.py update`.

</details>

## Using BIC

```python
import numpy as np
from bic import run_BIC

# f_i(x) = A_i log(B_i x + C_i), here sLLF utilities with laxities ell
xmax = np.array([11.0, 22.0, 11.0, 22.0])
ell = np.array([3.0, 5.0, 2.5, 8.0])
x, objective, seconds = run_BIC(budget=20.0, eps=1e-13, A=xmax, B=1 / xmax, C=ell - 1,
                                xmin=4.16, xmax=xmax)
```

## Proofs in Lean

`lean/` formalizes the theorems and lemmas of the paper in the Lean 4 proof assistant with Mathlib. Install Lean with [elan](https://github.com/leanprover/elan), then run from `lean/`:

```bash
lake exe cache get               # pre-built Mathlib (about 5 GB, once)
lake build                       # checks every proof (a few minutes)
lake env lean CheckAxioms.lean   # each result depends only on propext, Classical.choice, Quot.sound
```

On Windows, keep the repository on a short path (such as `C:\bic`). Mathlib's file paths can otherwise exceed the 260-character limit, and files are then skipped without an error; `lake exe cache unpack!` repairs this.

<details>
<summary>What is checked</summary>

Checked: Theorems 1 to 3, Lemmas 1 and 2 (with the strong duality of the restriction), Appendices A and B, the four utility families of Table I, the decomposition of (P) over cardinality vectors, Algorithm 1 with its count of at most $2(n_1+1)+n_2$ restrictions, Theorem 4 for two groups of maximum rates, and the multiplier bracket $[0, L]$ of Proposition 1.

Not checked: Theorem 4 for one group and for more than two groups, the runtime bounds of Proposition 1, the bisection loops as iterations with their tolerances, and Section III.

Modelling choices: Assumption 1 asks for two-sided derivatives at the end points of $[0, x_i^{\max}]$. Outside $[f_i'(x_i^{\max}), f_i'(0)]$, the projection of $(f_i')^{-1}(\lambda)$ is $x^{\min}$ for $\lambda > f_i'(0)$, and $x_i^{\max}$ for $\lambda < f_i'(x_i^{\max})$. The priority order of Assumption 2 is a fixed labeling of the EVs, and Lean's groups 0 and 1 are the paper's groups 1 and 2.

</details>

## Files

<details>
<summary>File tree</summary>

```
bic/
  bic.py                  BIC
  benchmarks.py           MIP (MOSEK) and the heuristics HB1 and HB2
  simulator.py            online simulation of a station over one day
  plotting.py             figure style
scripts/
  opt_*.py                Fig. 1
  scal_*.py               Fig. 2
  pico_*.py               Fig. 3
  cap_*.py                Figs. 4 and 5
  dr_*.py                 Fig. 6
  common.py               data loading for Figs. 4 to 6
  prep_sessions.py        builds data/sessions_utrecht_filtered.csv
  openev_share.py         share of 11 and 22 kW ratings (Sec. II)
firmware/
  bic_core.c, .h          BIC in C
  bic_service.c, .h       request handling
  main_wifi.c, ota.c      Pico firmware, updates over WiFi
  host/bench_host.c       timing of the C code on the PC
data/
  sessions_utrecht_raw.csv
  open-ev-data-v1.24.0.json
results/                  results of the paper
lean/BicLean/
  Prefix.lean             restriction, its optimal value, priority order; Theorem 2
  Everett.lean            Theorem 1, fast-path bound
  KeyFamily.lean          Appendix A
  TableI.lean             Table I
  ClosedForm.lean         Appendix B
  Duality.lean            strong duality of the restriction, Lemma 1, multiplier bracket of Proposition 1
  Diminishing.lean        Lemma 2, Theorem 3
  Choose.lean             Algorithm 1
  Correctness.lean        decomposition of (P), Theorem 1 and fast-path of Algorithm 2, Theorem 4
lean/CheckAxioms.lean     lists the axioms behind each result
```

</details>

## Data

- `data/sessions_utrecht_raw.csv`: K. de Bont et al., "Electric Vehicle Charging Session Data of Large Office Parking Lot," 4TU.ResearchData, 2024, [doi:10.4121/80ef3824-3f5d-4e45-8794-3b8791efbd13.v1](https://doi.org/10.4121/80ef3824-3f5d-4e45-8794-3b8791efbd13.v1), licensed under [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/). The sessions file and the results derived from it (`results/cap_*.csv`, `results/dr_*.csv`) are under the same licence.
- `data/open-ev-data-v1.24.0.json`: [OpenEV Data](https://github.com/open-ev-data/open-ev-data-dataset/releases/tag/v1.24.0), release v1.24.0, licensed under CDLA-Permissive-2.0 (`data/LICENSE-OpenEV.md`).

Licence: MIT.
