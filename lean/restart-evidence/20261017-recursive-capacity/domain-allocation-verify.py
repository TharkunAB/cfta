#!/usr/bin/env python3
"""Check frozen component hashes and final imported probe diagnostics."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / 'domain-allocation-manifest.json').read_text())
for entry in manifest['files']:
    path = root / entry['path']
    data = path.read_bytes()
    assert len(data) == entry['bytes'], path
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], path
for source, log, pairs in [
    ('domain-allocation-public.lean', 'domain-allocation-public-2.log', 35),
    ('domain-allocation-kernels.lean', 'domain-allocation-kernels-4.log', 4),
]:
    text = (evidence / source).read_text()
    output = (evidence / log).read_text()
    assert text.count('#print axioms ') == pairs, source
    assert text.count('#check @') == pairs, source
    assert not re.search(r'error(?:\(|:)|warning:|sorryAx', output), log
    for setting in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                    'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert f'set_option {setting}' in text, (source, setting)
for log in ['domain-allocation-cache-direct-3.log', 'domain-allocation-domain-direct-2.log']:
    assert (evidence / log).read_bytes() == b'', log
for source in ['domain-allocation-public.lean', 'domain-allocation-kernels.lean',
               'domain-allocation-review.md']:
    data = (evidence / source).read_bytes()
    assert data.endswith(b'\n') and not data.endswith(b'\n\n'), source
print(f"PASS: {len(manifest['files'])} frozen hashes; 35 public pairs; 4 integration pairs; final logs clean")
