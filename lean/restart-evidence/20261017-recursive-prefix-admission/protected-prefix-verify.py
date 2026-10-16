#!/usr/bin/env python3
"""Verify frozen finish-prefix sources and their final imported probes."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / 'protected-prefix-manifest.json').read_text())
for entry in manifest['files']:
    data = (root / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
for source, log, pairs in [
    ('protected-prefix-public.lean', 'protected-prefix-public-1.log', 10),
    ('protected-prefix-kernels.lean', 'protected-prefix-kernels-2.log', 2),
]:
    text = (evidence / source).read_text()
    assert text.count('#print axioms ') == pairs, source
    assert text.count('#check @') == pairs, source
    assert not re.search(r'error(?:\(|:)|warning:|sorryAx', (evidence / log).read_text()), log
    for setting in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                    'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert f'set_option {setting}' in text, (source, setting)
    data = (evidence / source).read_bytes()
    assert data.endswith(b'\n') and not data.endswith(b'\n\n'), source
for attempt in range(1, 4):
    assert (evidence / f'protected-prefix-direct-{attempt}.log').read_bytes() == b''
print(f"PASS: {len(manifest['files'])} frozen hashes; 10 public pairs; 2 integration pairs; final logs clean")
