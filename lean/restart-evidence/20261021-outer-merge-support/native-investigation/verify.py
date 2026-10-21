#!/usr/bin/env python3
"""Check this source audit without running Lean."""
import argparse
import hashlib
import json
from pathlib import Path


def pin(path: Path, entry: dict) -> None:
    assert path.is_file(), str(path)
    data = path.read_bytes()
    assert len(data) == entry['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'manifest.json').read_text())
    for entry in manifest['files']:
        pin(here / entry['path'], entry)
    sources = json.loads((here / 'source-pins.json').read_text())['files']
    for entry in sources:
        pin(here / 'inputs/root' / entry['path'], entry)
        if args.live:
            pin(args.root / entry['path'], entry)
    report = (here / 'investigation.md').read_text()
    for exact in ['unchecked theorem proposal', 'BinderFree event.expression',
                  'SAME actual publication', 'PositiveAt event.body path',
                  'PositiveAt event.ordinary path', 'initial PositionCorrect heap',
                  'No full nested pointwise law is claimed', 'No actual completed original-source counterexample']:
        assert exact in report, exact
    assert not list(here.glob('*.lean'))
    print(json.dumps({'status': 'PASS', 'live': args.live,
                      'local_pins': len(manifest['files']), 'root_pins': len(sources),
                      'new_lean_jobs': 0, 'new_public_pairs': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
