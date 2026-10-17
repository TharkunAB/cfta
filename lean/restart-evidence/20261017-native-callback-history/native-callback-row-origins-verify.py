#!/usr/bin/env python3
"""Verify the actual callback row-origin component and its capped evidence."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'native-callback-row-origins'
manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.is_file(), item['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], item['path']
assert (ROOT / manifest['production']).read_bytes() == (HERE / (PREFIX + '-direct-2.source.lean')).read_bytes()
strict = json.loads((HERE / (PREFIX + '-direct-2.json')).read_text())
assert strict['exit_code'] == 0
assert (HERE / strict['log']).stat().st_size == 0
assert strict['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
assert strict['command'][1] == '-Dlinter.all=true'
assert strict['command'][-1] == str(HERE / strict['source'])
failed = json.loads((HERE / (PREFIX + '-direct-1.json')).read_text())
assert failed['exit_code'] == 1
assert (HERE / failed['log']).stat().st_size > 0
for path in HERE.glob(PREFIX + '-*.limits.json'):
    assert json.loads(path.read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
canonical = json.loads((HERE / (PREFIX + '-canonical-1.json')).read_text())
assert canonical['exit_code'] == 0
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (553 jobs).' in log
assert not any(x in log for x in ['warning:', 'error:', 'sorryAx'])
flags = ['set_option linter.all true', 'set_option pp.all true',
         'set_option pp.explicit true', 'set_option pp.fullNames true',
         'set_option pp.proofs true', 'set_option pp.proofs.threshold 254',
         'set_option pp.universes true', 'set_option pp.deepTerms true',
         'set_option pp.maxSteps 10000000']
pairs = 0
for group in json.loads((HERE / (PREFIX + '-selected.json')).read_text()):
    stem = group['stem']
    source = (HERE / (stem + '.source.lean')).read_text()
    output = (HERE / (stem + '.log')).read_text()
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0
    assert all(flag in source for flag in flags)
    assert not any(x in output for x in ['warning:', 'error:', 'sorryAx', '⋯', '…', '...', 'truncated'])
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
    assert len(axioms) == group['pairs']
    for record in axioms:
        names = [re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in record.split(',') if name.strip()]
        assert set(names) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for name in group['names']:
        assert '#check @' + name in source
        assert '#print ' + name + '\n' in source
        assert '#print axioms ' + name in source
    pairs += group['pairs']
assert pairs == manifest['public_pairs'] == 2
print(f"PASS: {len(manifest['files'])} pinned files; 2 full public pairs; actual 4 GiB limits")
