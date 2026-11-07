"""Fig. 3 data: BIC on the Raspberry Pi Pico 2 W over WiFi, on the instances
of Fig. 2 sent as EV states. Each allocation is checked against run_BIC.

Usage: python scripts/pico_run.py [--host IP]
Output: results/pico_wifi.csv
"""
import argparse
import os
import socket
import struct
import sys
import time
import warnings
from concurrent.futures import ThreadPoolExecutor

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import bic

CASES = 'results/scal_instances.npz'
CSV_PATH = 'results/pico_wifi.csv'
EPS = 1e-13
TCP_PORT = 4242
PATHS = {0: 'all-max', 1: 'fast', 2: 'choose'}
REQ = struct.Struct('<4sIII4d')       # see firmware/bic_service.h
REP = struct.Struct('<4siIIIIIIQQd')


class TcpLink:
    def __init__(self, host, port, timeout):
        self.sock = socket.create_connection((host, port), timeout=timeout)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)

    def write(self, data):
        self.sock.sendall(data)

    def read(self, size):
        buf = bytearray()
        while len(buf) < size:
            chunk = self.sock.recv(size - len(buf))
            if not chunk:
                raise ConnectionError('connection closed')
            buf += chunk
        return bytes(buf)


def pack_request(magic, arrays, budget, xmin, xmax, reps=1, fastpath=True, eps=EPS):
    n = len(arrays[0])
    payload = REQ.pack(magic, n, reps, int(fastpath) << 1, budget, eps, xmin, xmax)
    for v in arrays:
        payload += np.ascontiguousarray(v, dtype='<f8').tobytes()
    return payload


def exchange(link, payload):
    """Send a request; return (reply, x, round trip [s])."""
    t0 = time.perf_counter()
    link.write(payload)
    fields = REP.unpack(link.read(REP.size))
    n_out = fields[2]
    x = np.frombuffer(link.read(8 * n_out), dtype='<f8') if n_out else np.zeros(0)
    rt = time.perf_counter() - t0
    magic, status, _, path, c_best, chain_ok, sys_hz, reps_out, t_min, t_total, objval = fields
    if magic != b'BICR':
        raise RuntimeError(f'unexpected reply {magic!r}')
    reply = dict(status=status, path=PATHS.get(path, path), c_best=c_best,
                 chain_ok=chain_ok & 0xFFFF, n_groups=chain_ok >> 16,
                 sys_hz=sys_hz, reps=reps_out,
                 t_chip_min_s=t_min * 1e-6, t_chip_mean_s=t_total * 1e-6 / max(reps_out, 1),
                 objval=objval)
    return reply, x, rt


def ping(link):
    return exchange(link, pack_request(b'BICQ', ([], [], []), 0.0, 1.0, 1.0))


def scan_for_pico(port=TCP_PORT, timeout=0.5):
    """First address on the local /24 network that answers a ping on port 4242."""
    probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    probe.connect(('10.255.255.255', 1))
    prefix = probe.getsockname()[0].rsplit('.', 1)[0]
    probe.close()

    def is_open(host):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.settimeout(timeout)
            return host if s.connect_ex((host, port)) == 0 else None

    with ThreadPoolExecutor(max_workers=64) as pool:
        hosts = [h for h in pool.map(is_open, [f'{prefix}.{i}' for i in range(1, 255)]) if h]
    for host in hosts:
        try:
            if ping(TcpLink(host, port, 2.0))[0]['status'] == 0:
                return host
        except (OSError, RuntimeError, struct.error):
            continue
    raise SystemExit(f'No Pico found on {prefix}.0/24; pass --host')


def ev_states(lax, n, rep, xmax):
    """Remaining energy drawn per EV and parking time t = laxity + 60 e / xmax."""
    e_rem = np.random.default_rng(1000 * n + rep).uniform(5.0, 40.0, n)
    t_rem = lax + 60.0 * e_rem / xmax
    return t_rem, e_rem


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--host', default='scan')
    args = ap.parse_args()
    host = scan_for_pico() if args.host == 'scan' else args.host
    link = TcpLink(host, TCP_PORT, 900.0)

    pings = np.array([ping(link)[2] for _ in range(100)])
    print(f'{host}: ping median {1e3 * np.median(pings):.2f} ms')

    d = np.load(CASES)
    xmin = float(d['meta_xmin'])
    warnings.simplefilter('ignore')
    rows = []
    for n in [int(v) for v in d['meta_ns']]:
        for r in range(5):
            key = f'n{n}_r{r}'
            budget = float(d[f'{key}_budget_kw'])
            xmax_ev = np.asarray(d[f'{key}_xmax'], dtype=float)
            for regime in ('gap', 'no_gap'):
                lax = d[f'{key}_{regime}_laxity']
                t_rem, e_rem = ev_states(lax, n, r, xmax_ev)
                req = pack_request(b'EVSM', (t_rem, e_rem, xmax_ev), budget, xmin,
                                   float(np.max(xmax_ev)))
                reply, x, rt = exchange(link, req)
                if reply['status'] != 0:
                    raise RuntimeError(f'{key} {regime}: status {reply["status"]}')

                A, B = xmax_ev.copy(), 1.0 / xmax_ev
                C = np.maximum(t_rem - 60.0 * e_rem / xmax_ev - 1.0, 1e-6)
                t_pc = time.perf_counter()
                x_py, obj_py, _ = bic.run_BIC(budget, EPS, A, B, C, xmin, xmax_ev)
                t_pc = time.perf_counter() - t_pc
                dx = float(np.max(np.abs(x - x_py)))
                dobj = abs(reply['objval'] - obj_py) / max(1.0, abs(obj_py))

                rows.append(dict(n=n, rep=r, regime=regime, budget_kw=budget, link='wifi',
                                 round_trip_s=rt, ping_median_s=float(np.median(pings)),
                                 t_pc_python_s=t_pc, max_abs_dx_kw=dx,
                                 rel_obj_diff=dobj, **reply))
                print(f'n={n:5d} r={r} {regime:6s}: chip {1e3 * reply["t_chip_min_s"]:.3f} ms, '
                      f'round trip {1e3 * rt:.3f} ms, max|dx| {dx:.1e} kW', flush=True)
    pd.DataFrame(rows).to_csv(CSV_PATH, index=False)


if __name__ == '__main__':
    main()
