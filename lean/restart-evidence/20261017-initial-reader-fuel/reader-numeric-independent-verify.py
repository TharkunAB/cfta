#!/usr/bin/env python3
"""Verify final numeric-reader review inputs without rebuilding."""
from pathlib import Path
import hashlib
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
m=json.loads((HERE/'reader-numeric-independent-manifest.json').read_text())
assert len(m['entries'])==m['entry_count']
for e in m['entries']:
 data=(ROOT/e['path']).read_bytes()
 assert len(data)==e['bytes'],e['path']
 assert hashlib.sha256(data).hexdigest()==e['sha256'],e['path']
print('PASS:',m['entry_count'],'hashes; final numeric-reader review inputs unchanged')
