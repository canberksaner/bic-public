"""Fig. 3 data: the firmware's C code (bic_service.c, bic_core.c) timed on the
PC on the same requests as pico_run.py, fastest of 5 runs. Windows, compiled
with zig cc -O3.

Output: results/pico_pc.csv
"""
import ctypes
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
from pico_run import ev_states, pack_request

CASES = 'results/scal_instances.npz'
CSV_PATH = 'results/pico_pc.csv'
FIRMWARE = Path(__file__).resolve().parents[1] / 'firmware'
REPS = 5


def build_bench():
    out = Path(tempfile.gettempdir()) / 'bic_bench.dll'
    subprocess.run([sys.executable, '-m', 'ziglang', 'cc', '-O3', '-shared', '-DBIC_SHARED',
                    '-DBIC_HOST_TEST', '-DBIC_MAX_N=3500', '-o', str(out),
                    str(FIRMWARE / 'bic_service.c'), str(FIRMWARE / 'bic_core.c'),
                    str(FIRMWARE / 'host' / 'bench_host.c')], check=True)
    lib = ctypes.CDLL(str(out))
    lib.bench_request.argtypes = [ctypes.c_char_p, ctypes.c_uint64, ctypes.c_uint32,
                                  ctypes.POINTER(ctypes.c_int32)]
    lib.bench_request.restype = ctypes.c_double
    return lib


def main():
    d = np.load(CASES)
    xmin = float(d['meta_xmin'])
    lib = build_bench()
    rows = []
    for n in [int(v) for v in d['meta_ns']]:
        for rep in range(5):
            key = f'n{n}_r{rep}'
            budget = float(d[f'{key}_budget_kw'])
            xmax_ev = np.asarray(d[f'{key}_xmax'], dtype=float)
            for regime in ('gap', 'no_gap'):
                t_rem, e_rem = ev_states(d[f'{key}_{regime}_laxity'], n, rep, xmax_ev)
                req = pack_request(b'EVSM', (t_rem, e_rem, xmax_ev), budget, xmin,
                                   float(np.max(xmax_ev)))
                status = ctypes.c_int32()
                best = lib.bench_request(req, len(req), REPS, ctypes.byref(status))
                if best < 0 or status.value != 0:
                    raise RuntimeError(f'{key} {regime}: {best}, status {status.value}')
                rows.append(dict(n=n, rep=rep, regime=regime, t_pc_min_s=best))
                print(f'n={n:5d} r={rep} {regime:6s}: {1e3 * best:.4f} ms', flush=True)
    pd.DataFrame(rows).to_csv(CSV_PATH, index=False)


if __name__ == '__main__':
    main()
