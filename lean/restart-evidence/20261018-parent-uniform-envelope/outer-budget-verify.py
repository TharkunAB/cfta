#!/usr/bin/env python3
"""Verify frozen outer Parent-site workload evidence without running Lean."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'outer-budget-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
selection = json.loads((HERE / 'outer-budget-selection.json').read_text())
assert selection['strict'] == 'outer-budget-direct-4'
assert selection['kernel_strict'] == 'outer-budget-kernels-2'
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
lean = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
expected = {'outer-budget-direct-1': 1, 'outer-budget-direct-2': 1,
            'outer-budget-direct-3': 0, 'outer-budget-direct-4': 0,
            'outer-budget-kernels-1': 1, 'outer-budget-kernels-2': 0,
            'outer-budget-public-1': 0, 'outer-budget-kernels-public-1': 0}
for stem, status in expected.items():
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == status, stem
    assert json.loads((HERE / receipt['limits']).read_text()) == limits, stem
    snapshot = HERE / receipt['source']
    assert receipt['command'] == [lean, '-Dlinter.all=true', str(snapshot)], stem
    assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == receipt['sha256'], stem
    assert receipt['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'], stem
for stem in [selection['strict'], selection['kernel_strict']]:
    assert (HERE / (stem + '.log')).read_bytes() == b'', stem
production = ROOT / selection['production']
assert production.read_bytes() == (HERE / (selection['strict'] + '.source.lean')).read_bytes()
assert hashlib.sha256(production.read_bytes()).hexdigest() == selection['production_sha256']

canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
assert canonical['exit_code'] == 0
assert json.loads((HERE / canonical['limits']).read_text()) == limits
assert canonical['command'] == ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake',
                                 '-d', str(ROOT / 'lean'), 'build', 'MicroCFTA.SourceCurrentOuterCallBudget']
assert canonical['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
assert 'Build completed successfully' in (HERE / canonical['log']).read_text()

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
counts = {'public': 0, 'constructed': 0}
for group in selection['selected_groups']:
    stem, count = group['name'], group['pairs']
    source = (HERE / (stem + '.source.lean')).read_text()
    output = (HERE / (stem + '.log')).read_text()
    assert group['full_proof'] is True
    counts[group['kind']] += count
    for option in options:
        assert 'set_option ' + option in source, (stem, option)
    heads = re.findall(r'^#check @([^\s]+)$', source, re.M)
    assert len(heads) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
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
assert counts == {'public': 9, 'constructed': 1}
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), **counts,
                  'strict_empty': True, 'effective_memory_bytes': 4294967296,
                  'effective_swap_bytes': 0, 'preserved_failed_attempts': 3}))
