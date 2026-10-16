#!/usr/bin/env python3
"""Check reviewed sources and final imported probes."""
from pathlib import Path
import hashlib
import json
import re
root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / 'body-yield-manifest.json').read_text())
for entry in manifest['files']:
    data = (root / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
for source, log, pairs in [
    ('body-yield-public.lean', 'body-yield-public-1.log', 2),
    ('body-yield-kernels.lean', 'body-yield-kernels-4.log', 2),
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
print(f"PASS: {len(manifest['files'])} frozen hashes; 2 public pairs; 2 integration pairs; final logs clean")
