#!/usr/bin/env python3
"""Verify the frozen Parent integration evidence without running Lean."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'parent-selected-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

selection = json.loads((HERE / 'parent-selected-selection.json').read_text())
assert selection['strict'] == 'parent-selected-kernels-3'
assert (HERE / (selection['strict'] + '.log')).read_bytes() == b''
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for receipt_path in HERE.glob('parent-selected-*.json'):
    receipt = json.loads(receipt_path.read_text())
    if 'exit_code' not in receipt:
        continue
    assert json.loads((HERE / receipt['limits']).read_text()) == limits, receipt_path.name
    if 'source' in receipt:
        snapshot = HERE / receipt['source']
        assert receipt['command'] == ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
                                      '-Dlinter.all=true', str(snapshot)], receipt_path.name
        assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == receipt['sha256'], receipt_path.name
for stem in ['parent-selected-kernels-1', selection['strict'], 'parent-selected-public-1']:
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0, stem
assert json.loads((HERE / 'parent-selected-kernels-2.json').read_text())['exit_code'] == 1

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
for group in selection['groups']:
    stem, count = group['name'], group['pairs']
    source = (HERE / (stem + '.source.lean')).read_text()
    output = (HERE / (stem + '.log')).read_text()
    assert group['kind'] == 'constructed' and group['full_proof'] is True
    for option in options:
        assert 'set_option ' + option in source, (stem, option)
    heads = re.findall(r'^#check @([^\s]+)$', source, re.M)
    assert len(heads) == count, stem
    for head in heads:
        assert '#print ' + head + '\n' in source, (stem, head)
        assert '#print axioms ' + head + '\n' in source, (stem, head)
    for bad in ['sorryAx', 'failed to pretty print', '⋯', '…', '...', 'truncated', 'error:', 'warning:']:
        assert bad not in output, (stem, bad)
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    reports += [(head, '') for head in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    assert len(reports) == count and {head for head, _ in reports} == set(heads), stem
    for head, axioms in reports:
        plain = re.sub(r'\.\{[^}]*\}', '', axioms)
        assert {name.strip() for name in plain.split(',') if name.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, (head, axioms)

for module, direct, canonical in [
    ('SourceCurrentActualParentRowOrigins', 'parent-origin-direct-3', 'parent-origin-canonical-3')]:
    assert (ROOT / 'lean/MicroCFTA' / (module + '.lean')).read_bytes() == (HERE / (direct + '.source.lean')).read_bytes()
    assert (HERE / (direct + '.log')).read_bytes() == b''
    for stem in [direct, canonical]:
        receipt = json.loads((HERE / (stem + '.json')).read_text())
        assert receipt['exit_code'] == 0 and json.loads((HERE / receipt['limits']).read_text()) == limits
    assert 'Build completed successfully' in (HERE / (canonical + '.log')).read_text()
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'constructed_pairs': 2,
                  'strict_empty': True, 'effective_memory_bytes': 4294967296, 'effective_swap_bytes': 0,
                  'preserved_failed_attempts': 1}))
