#!/usr/bin/env python3
"""Verify this source-pinned design package without running Lean."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
parser.add_argument('--live', action='store_true')
args = parser.parse_args()
here = Path(__file__).resolve().parent

def read_json(name):
    return json.loads((here / name).read_text())

def check(base, item):
    raw = (base / item['path']).read_bytes()
    assert len(raw) == item['bytes'], item['path']
    assert hashlib.sha256(raw).hexdigest() == item['sha256'], item['path']

manifest = read_json('plan-manifest.json')
for item in manifest['files']:
    check(here, item)
pins = read_json('plan-source-pins.json')['files']
for item in pins:
    check(here / 'inputs', item)
    if args.live:
        check(args.root, item)
assert (manifest['owned_lean_jobs'], manifest['owned_public_pairs'], manifest['owned_constructed_pairs']) == (0, 0, 0)
text = (here / 'plan.md').read_text()
for phrase in ['Design only.', 'proposed theorem is unproved', 'h<g<n', 'Closed non-Mu captures:', 'Warm generated binder winners:', 'Self replacement:', 'Global termination and Haskell refinement remain open.']:
    assert phrase in text, phrase
print(json.dumps(dict(status='PASS', mode='live' if args.live else 'portable', root_pins=len(pins), local_pins=len(manifest['files']), owned_lean_jobs=0, owned_public_pairs=0, owned_constructed_pairs=0), indent=2))
