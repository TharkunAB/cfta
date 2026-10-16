#!/usr/bin/env python3
"""Check the final linter correction and its immutable predecessor."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / 'protected-prefix-linter-final-manifest.json').read_text())
for entry in manifest['files']:
    data = (root / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
assert hashlib.sha256((evidence / 'protected-prefix-manifest.json').read_bytes()).hexdigest() == \
    'f87702113038b0058ad0265d4f022a0620a2bfbf96fae32ad64ed2ee766840d0'
assert hashlib.sha256((evidence / 'protected-prefix-before-linter.source.lean').read_bytes()).hexdigest() == \
    '10c94c24f825b70b2443e32a18ceb10f6faec69133a912153458d6ba820833b0'
for log in ['protected-prefix-linter-final-direct-1.log', 'root-strict-protected-final.log']:
    assert (evidence / log).read_bytes() == b'', log
for source, log, pairs in [
    ('protected-prefix-public.lean', 'protected-prefix-linter-final-public-1.log', 10),
    ('protected-prefix-kernels.lean', 'protected-prefix-linter-final-kernels-1.log', 2),
]:
    text = (evidence / source).read_text()
    assert text.count('#print axioms ') == pairs, source
    assert text.count('#check @') == pairs, source
    assert not re.search(r'error(?:\(|:)|warning:|sorryAx', (evidence / log).read_text()), log
assert (evidence / 'protected-prefix-public-1.log').read_bytes() == \
    (evidence / 'protected-prefix-linter-final-public-1.log').read_bytes()
print(f"PASS: {len(manifest['files'])} final/historical hashes; all-linter source clean; identical 10 public pairs; 2 integration pairs")
