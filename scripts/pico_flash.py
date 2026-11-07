"""Build and load the Pico firmware (Windows, tools in ~/.pico-sdk).

  setup    once, over USB: partition table and first image
  update   over WiFi, into the free partition
  version  firmware version and partition

Usage: python scripts/pico_flash.py setup|update|version [--host IP]
"""
import argparse
import os
import struct
import subprocess
import sys
import time
import zlib
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from pico_run import TCP_PORT, TcpLink, scan_for_pico

FIRMWARE = Path(__file__).resolve().parents[1] / 'firmware'
BUILD = FIRMWARE / 'build'
PICO_SDK_HOME = Path.home() / '.pico-sdk'
PICOTOOL = PICO_SDK_HOME / 'picotool' / '2.3.1' / 'picotool' / 'picotool.exe'
CMAKE = PICO_SDK_HOME / 'cmake' / 'v4.3.4' / 'bin' / 'cmake.exe'
NINJA_DIR = PICO_SDK_HOME / 'ninja' / 'v1.13.2'


def run(cmd):
    print('$', ' '.join(str(c) for c in cmd))
    subprocess.run([str(c) for c in cmd], check=True,
                   env={**os.environ, 'PATH': f'{NINJA_DIR}{os.pathsep}{os.environ["PATH"]}'})


def build():
    run([CMAKE, '-S', FIRMWARE, '-B', BUILD, '-G', 'Ninja', '-DCMAKE_BUILD_TYPE=Release'])
    run([CMAKE, '--build', BUILD, '--target', 'pico_bic_wifi'])
    return (BUILD / 'pico_bic_wifi_version.txt').read_text().strip()


def setup():
    version = build()
    run([PICOTOOL, 'partition', 'create', FIRMWARE / 'ota_pt.json', BUILD / 'ota_pt.uf2'])
    run([PICOTOOL, 'reboot', '-u', '-f'])
    time.sleep(3)
    run([PICOTOOL, 'erase', '-a'])
    run([PICOTOOL, 'load', BUILD / 'ota_pt.uf2'])
    run([PICOTOOL, 'reboot', '-u'])
    time.sleep(3)
    run([PICOTOOL, 'partition', 'info'])
    run([PICOTOOL, 'load', '-x', BUILD / 'pico_bic_wifi.uf2'])
    print(f'Loaded firmware {version}')


def query_version(host):
    link = TcpLink(host, TCP_PORT, 60.0)
    link.write(b'VERQ')
    magic, minor, major, partition = struct.unpack('<4sHHi', link.read(12))
    if magic != b'VERR':
        raise RuntimeError(f'unexpected reply {magic!r}')
    return f'{major}.{minor}', 'AB'[partition] if partition in (0, 1) else '-'


def update(host):
    version = build()
    image = (BUILD / 'pico_bic_wifi.bin').read_bytes()
    old_version, old_slot = query_version(host)
    link = TcpLink(host, TCP_PORT, 60.0)
    link.write(b'OTAQ' + struct.pack('<II', len(image), zlib.crc32(image)) + image)
    magic, status = struct.unpack('<4si', link.read(8))
    if magic != b'OTAR' or status != 0:
        raise SystemExit(f'update refused ({magic!r}, {status})')

    deadline = time.time() + 120
    while time.time() < deadline:
        time.sleep(3)
        try:
            new_version, new_slot = query_version(host)
            break
        except (OSError, RuntimeError, struct.error):
            continue
    else:
        raise SystemExit('The Pico did not come back within 2 minutes.')
    ok = new_version == version and new_slot != old_slot
    print(f'{"updated" if ok else "update failed"}: {new_version} in slot {new_slot}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('action', choices=['setup', 'update', 'version'])
    ap.add_argument('--host', default='scan')
    args = ap.parse_args()
    if args.action == 'setup':
        setup()
        return
    host = scan_for_pico() if args.host == 'scan' else args.host
    if args.action == 'update':
        update(host)
    else:
        print(host, *query_version(host))


if __name__ == '__main__':
    main()
