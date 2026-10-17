#!/usr/bin/env python3
"""Verify immutable proof bytes and the selected capped Lean checks."""
from pathlib import Path
import hashlib
import json
import re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'union-local-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.is_file(), item['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], item['path']
for item in manifest['production']:
    path = ROOT / item['path']
    snapshot = HERE / (item['strict'] + '.source.lean')
    assert path.read_bytes() == snapshot.read_bytes(), item['path']
for stem in manifest['strict']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert (HERE / (stem + '.log')).stat().st_size == 0, stem
    assert meta['command'][-1] == str(HERE / (stem + '.source.lean')), stem
for stem in manifest['canonical']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit'] == 0 and meta['jobs'] > 0, stem
    lines = (HERE / (stem + '.log')).read_text().splitlines()
    assert lines[:3] == ['4294967296', '4294967296', '0'], stem
    assert not any(x in '\n'.join(lines) for x in ['error:', 'sorryAx']), stem
    warnings = [line for line in lines if line.startswith('warning:')]
    assert warnings == ["warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced."], stem
# Inspect every invocation's actual effective limits, including retained failures.
for path in HERE.glob('union-local-*.limits.json'):
    actual = json.loads(path.read_text())
    assert actual['memory.max'] == actual['memory.high'] == '4294967296', path.name
    assert actual['memory.swap.max'] == '0', path.name
flags = ['set_option linter.all true', 'set_option pp.all true', 'set_option pp.explicit true',
    'set_option pp.fullNames true', 'set_option pp.proofs true', 'set_option pp.proofs.threshold 254',
    'set_option pp.universes true', 'set_option pp.deepTerms true', 'set_option pp.maxSteps 10000000']
selected = json.loads((HERE / 'union-local-selected.json').read_text())
pairs = 0
for group in selected:
    stem = group['stem']
    meta = json.loads((HERE / (stem + '.json')).read_text())
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    assert meta['exit_code'] == 0, stem
    assert all(flag in source for flag in flags), stem
    assert not any(x in log for x in ['warning:', 'error:', 'sorryAx', '⋯', '…', '...', 'truncated']), stem
    groups = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(groups) == group['pairs'], stem
    for axioms in groups:
        names = [re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in axioms.split(',') if name.strip()]
        assert set(names) <= {'propext', 'Classical.choice', 'Quot.sound'}, (stem, names)
    for name in group['names']:
        assert '#check @' + name in source or '#check ' + name in source, name
        assert '#print axioms ' + name in source, name
        if group['public']:
            assert '#print ' + name + '\n' in source, name
    pairs += group['pairs']
assert pairs == 20
print(f"PASS: {len(manifest['files'])} pinned files, 8 production modules, 20 pairs / 3 groups, actual 4 GiB limits")
