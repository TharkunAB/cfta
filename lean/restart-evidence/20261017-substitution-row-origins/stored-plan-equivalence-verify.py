#!/usr/bin/env python3
"""Verify the immutable stored plan equivalence component."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'stored-plan-equivalence-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.is_file(), path
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
for stem in manifest['successful_checks']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    limits = json.loads((HERE / meta['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert str(source) == meta['command'][-1], stem
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean', stem
        assert '-Dlinter.all=true' in meta['command'], stem
        assert hashlib.sha256(source.read_bytes()).hexdigest() == meta['sha256'], stem
for stem in manifest['empty_logs']:
    assert (HERE / (stem + '.log')).stat().st_size == 0, stem
flags = ['linter.all true', 'pp.all true', 'pp.explicit true', 'pp.fullNames true',
         'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
         'pp.deepTerms true', 'pp.maxSteps 10000000']
for group in manifest['selected']:
    source = (HERE / (group['stem'] + '.source.lean')).read_text()
    raw = (HERE / (group['stem'] + '.log')).read_text()
    for flag in flags:
        assert 'set_option ' + flag in source, (group['stem'], flag)
    assert len(re.findall(r'^#check @', source, re.M)) == group['pairs'], group
    printed = re.findall(r"depends on axioms: \[([^\]]*)\]", raw, re.S)
    assert len(printed) == group['pairs'], group
    for axioms in printed:
        plain = re.sub(r'\.\{[^}]*\}', '', axioms)
        assert set(re.findall(r'[A-Za-z][A-Za-z.]*', plain)) <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
    for forbidden in ['warning:', 'error:', 'error(', 'sorryAx', '⋯', '…', '...', 'truncated']:
        assert forbidden not in raw, (group['stem'], forbidden)
    if group['full_proofs']:
        assert len(re.findall(r'^#print (?!axioms)', source, re.M)) == group['pairs'], group
assert manifest['public_pairs'] == 5 and manifest['integration_pairs'] == 2
assert 'Build completed successfully (174 jobs).' in (HERE / 'stored-plan-equivalence-canonical-1.log').read_text()
print('PASS: %d frozen files; 5 public pairs; 2 constructed integration pairs; effective 4 GiB limits.' % len(manifest['files']))
