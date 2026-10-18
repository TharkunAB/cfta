#!/usr/bin/env python3
"""Verify existing Classes carrier checks without rerunning Lean."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'classes-cross-review-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
s = json.loads((HERE / 'outer-context-classes-selection.json').read_text())
assert s['review_only'] and s['new_public_pairs'] == s['new_constructed_pairs'] == 0
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
toolchain = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'
stems = [s['strict'], s['kernel_strict'], *(g['name'] for g in s['selected_existing_groups'])]
for stem in stems + [s['canonical']]:
    r = json.loads((HERE / (stem + '.json')).read_text())
    assert r['exit_code'] == 0
    assert json.loads((HERE / r['limits']).read_text()) == limits
    assert r['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
    if stem != s['canonical']:
        path = HERE / r['source']
        assert r['command'] == [toolchain + 'lean', '-Dlinter.all=true', str(path)]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == r['sha256']
    else:
        assert r['command'] == [toolchain + 'lake', '-d', str(ROOT / 'lean'), 'build',
                                'MicroCFTA.SourceCurrentClassesGuardAlphabet']
        out = (HERE / r['log']).read_text()
        assert 'Build completed successfully' in out
        assert 'SourceCurrentClassesGuardAlphabet.lean:' not in out
for stem in [s['strict'], s['kernel_strict']]:
    assert (HERE / (stem + '.log')).read_bytes() == b''
data = (ROOT / s['production']).read_bytes()
assert hashlib.sha256(data).hexdigest() == s['production_sha256']
assert data == (HERE / (s['strict'] + '.source.lean')).read_bytes()
options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
counts = {'public': 0, 'constructed': 0}
for group in s['selected_existing_groups']:
    source = (HERE / (group['name'] + '.source.lean')).read_text()
    out = (HERE / (group['name'] + '.log')).read_text()
    assert group['full_proof'] is True
    for option in options:
        assert 'set_option ' + option in source
    heads = re.findall(r'^#check @([^\s]+)$', source, re.M)
    assert len(heads) == group['pairs']
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == len(heads)
    assert len(re.findall(r'^#print axioms ', source, re.M)) == len(heads)
    for head in heads:
        assert '#print ' + head + '\n' in source and '#print axioms ' + head + '\n' in source
    for bad in ['sorryAx', 'failed to pretty print', '⋯', '…', '...', 'truncated', 'error:', 'warning:',
                'error(', 'warning(', 'maximum recursion depth', 'maximum number of heartbeats', 'pp.rawOnError']:
        assert bad not in out, (group['name'], bad)
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", out)
    reports += [(h, '') for h in re.findall(r"'([^']+)' does not depend on any axioms", out)]
    assert len(reports) == len(heads) and {h for h, _ in reports} == set(heads)
    for head, axioms in reports:
        names = {n.strip() for n in re.sub(r'\.\{[^}]*\}', '', axioms).split(',') if n.strip()}
        assert names <= {'propext', 'Classical.choice', 'Quot.sound'}, (head, axioms)
    counts[group['kind']] += len(heads)
assert counts == {'public': 2, 'constructed': 1}
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'reviewed_existing_pairs': counts,
                  'new_public_pairs': 0, 'new_constructed_pairs': 0, 'lean_runs': 0}))
