#!/usr/bin/env python3
"""Check read-only source pins for the outer context proof map."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'outer-context-map-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
print(json.dumps({'status': 'PASS', 'source_pins': len(manifest['entries']) - 2,
                  'entries': len(manifest['entries']), 'lean_runs': 0,
                  'new_public_pairs': 0, 'new_constructed_pairs': 0}))
