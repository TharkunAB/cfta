#!/usr/bin/env python3
"""Verify finite-support proofs and their immutable capped evidence."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'comparison-finite-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.is_file(), item['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], item['path']
assert (ROOT / manifest['production']).read_bytes() == (HERE / 'comparison-finite-direct-2.source.lean').read_bytes()
strict = json.loads((HERE / 'comparison-finite-direct-2.json').read_text())
assert strict['exit_code'] == 0
assert (HERE / strict['log']).stat().st_size == 0
script = (HERE / 'comparison-finite-direct-2.sh').read_text()
assert 'lean4---v4.34.1/bin/lean -Dlinter.all=true ' in script
assert str(HERE / 'comparison-finite-direct-2.source.lean') in script
failed = json.loads((HERE / 'comparison-finite-direct-1.json').read_text())
assert failed['exit_code'] == 1
assert (HERE / failed['log']).read_text() == 'Failed to connect to bus: Operation not permitted\n'
for stem in ['comparison-finite-direct-2', 'comparison-finite-public-1']:
    assert (HERE / (stem + '.caps')).read_text().splitlines() == ['4294967296', '4294967296', '0']
canonical = json.loads((HERE / 'comparison-finite-canonical-1.json').read_text())
assert canonical['exit'] == 0 and canonical['jobs'] == 329
canonical_log = (HERE / 'comparison-finite-canonical-1.log').read_text()
assert canonical_log.splitlines()[:3] == ['4294967296', '4294967296', '0']
assert not any(token in canonical_log for token in ['warning:', 'error:', 'sorryAx'])
flags = ['set_option linter.all true', 'set_option pp.all true',
         'set_option pp.explicit true', 'set_option pp.fullNames true',
         'set_option pp.proofs true', 'set_option pp.proofs.threshold 254',
         'set_option pp.universes true', 'set_option pp.deepTerms true',
         'set_option pp.maxSteps 10000000']
pairs = 0
for group in json.loads((HERE / 'comparison-finite-selected.json').read_text()):
    stem = group['stem']
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0
    assert all(flag in source for flag in flags)
    assert not any(token in log for token in ['warning:', 'error:', 'sorryAx', '⋯', '…', '...', 'truncated'])
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(axioms) == group['pairs']
    for record in axioms:
        names = [re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in record.split(',') if name.strip()]
        assert set(names) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for name in group['names']:
        assert '#check @' + name in source
        assert '#print ' + name + '\n' in source
        assert '#print axioms ' + name in source
    pairs += group['pairs']
assert pairs == manifest['public_pairs'] == 3
print(f"PASS: {len(manifest['files'])} pinned files; 3 full public pairs; actual 4 GiB limits")
