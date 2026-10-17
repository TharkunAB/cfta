#!/usr/bin/env python3
"""Verify the full outer transport and its immutable capped proof evidence."""
from pathlib import Path
import hashlib
import json
import re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'outer-normal-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.is_file(), item['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], item['path']
assert (ROOT / manifest['production']).read_bytes() == (HERE / 'outer-normal-direct-2.source.lean').read_bytes()
for stem in manifest['strict']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert (HERE / (stem + '.log')).stat().st_size == 0, stem
    assert meta['command'][-1] == str(HERE / (stem + '.source.lean')), stem
for path in HERE.glob('outer-normal-*.limits.json'):
    limits = json.loads(path.read_text())
    assert limits['memory.max'] == limits['memory.high'] == '4294967296', path.name
    assert limits['memory.swap.max'] == '0', path.name
meta = json.loads((HERE / 'outer-normal-canonical-1.json').read_text())
assert meta['exit'] == 0 and meta['jobs'] == 1461
lines = (HERE / 'outer-normal-canonical-1.log').read_text().splitlines()
assert lines[:3] == ['4294967296', '4294967296', '0']
assert not any(x in '\n'.join(lines) for x in ['error:', 'sorryAx'])
assert [line for line in lines if line.startswith('warning:')] == [
    'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.']
flags = ['set_option linter.all true', 'set_option pp.all true', 'set_option pp.explicit true',
    'set_option pp.fullNames true', 'set_option pp.proofs true', 'set_option pp.proofs.threshold 254',
    'set_option pp.universes true', 'set_option pp.deepTerms true', 'set_option pp.maxSteps 10000000']
pairs = 0
for group in json.loads((HERE / 'outer-normal-selected.json').read_text()):
    stem = group['stem']
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0, stem
    assert all(flag in source for flag in flags), stem
    assert not any(x in log for x in ['warning:', 'error:', 'sorryAx', '⋯', '…', '...', 'truncated']), stem
    groups = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(groups) == group['pairs'], stem
    for axioms in groups:
        names = [re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in axioms.split(',') if name.strip()]
        assert set(names) <= {'propext', 'Classical.choice', 'Quot.sound'}, (stem, names)
    for name in group['names']:
        assert '#check @' + name in source, name
        assert '#print axioms ' + name in source, name
        if group['public']:
            assert '#print ' + name + '\n' in source, name
    pairs += group['pairs']
assert pairs == 10
print(f"PASS: {len(manifest['files'])} pinned files, 8 public + 2 constructed pairs / 3 groups, actual 4 GiB limits")
