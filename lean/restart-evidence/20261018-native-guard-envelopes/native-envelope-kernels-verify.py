#!/usr/bin/env python3
"""Verify the frozen native guard envelope integration without running Lean."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'native-envelope-kernels-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

selection = json.loads((HERE / 'native-envelope-kernels-selection.json').read_text())
assert selection['selected_attempt'] == 2
strict = 'native-envelope-kernels-' + str(selection['selected_attempt'])
assert (HERE / (strict + '.log')).read_bytes() == b''
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
lean = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
for stem in ['native-envelope-kernels-1', strict, 'native-envelope-kernels-public-1']:
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == 0, stem
    assert json.loads((HERE / receipt['limits']).read_text()) == limits, stem
    snapshot = HERE / receipt['source']
    assert receipt['command'] == [lean, '-Dlinter.all=true', str(snapshot)], stem
    assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == receipt['sha256'], stem
    assert receipt['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
assert selection['preserved_failed'] == []
assert selection['preserved_successful_prefix'] == [1]

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
for group in selection['selected_groups']:
    stem, count = group['name'], group['pairs']
    source = (HERE / (stem + '.source.lean')).read_text()
    output = (HERE / (stem + '.log')).read_text()
    assert group['kind'] == 'constructed' and group['full_proof'] is True
    for option in options:
        assert 'set_option ' + option in source, (stem, option)
    heads = re.findall(r'^#check @([^\s]+)$', source, re.M)
    assert len(heads) == count == 1, stem
    assert heads == selection['declarations']
    for head in heads:
        assert '#print ' + head + '\n' in source, (stem, head)
        assert '#print axioms ' + head + '\n' in source, (stem, head)
    for bad in ['sorryAx', 'failed to pretty print', '⋯', '…', '...', 'truncated',
                'error:', 'warning:', 'error(', 'warning(', 'maximum recursion depth',
                'maximum number of heartbeats', 'pp.rawOnError']:
        assert bad not in output, (stem, bad)
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    reports += [(head, '') for head in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    assert len(reports) == count and {head for head, _ in reports} == set(heads), stem
    for head, axioms in reports:
        plain = re.sub(r'\.\{[^}]*\}', '', axioms)
        assert {name.strip() for name in plain.split(',') if name.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, (head, axioms)

for module, direct, canonical in [
    ('SourceCurrentGuardHeapBounds', 'guard-heap-direct-2', 'guard-heap-canonical-1'),
    ('SourceCurrentNativeGuardEnvelope', 'native-envelope-direct-1', 'native-envelope-canonical-1')]:
    production = ROOT / 'lean/MicroCFTA' / (module + '.lean')
    assert production.read_bytes() == (HERE / (direct + '.source.lean')).read_bytes()
    assert hashlib.sha256(production.read_bytes()).hexdigest() == selection['reviewed_production'][module + '.lean']
    assert (HERE / (direct + '.log')).read_bytes() == b''
    for stem in [direct, canonical]:
        receipt = json.loads((HERE / (stem + '.json')).read_text())
        assert receipt['exit_code'] == 0 and json.loads((HERE / receipt['limits']).read_text()) == limits
        assert receipt['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
    direct_receipt = json.loads((HERE / (direct + '.json')).read_text())
    assert direct_receipt['command'] == [lean, '-Dlinter.all=true', str(HERE / (direct + '.source.lean'))]
    canonical_receipt = json.loads((HERE / (canonical + '.json')).read_text())
    assert canonical_receipt['command'] == ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake',
                                            '-d', str(ROOT / 'lean'), 'build', 'MicroCFTA.' + module]
    assert 'Build completed successfully' in (HERE / (canonical + '.log')).read_text()
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'constructed_pairs': 1,
                  'strict_empty': True, 'effective_memory_bytes': 4294967296, 'effective_swap_bytes': 0,
                  'preserved_failed_attempts': 0}))
