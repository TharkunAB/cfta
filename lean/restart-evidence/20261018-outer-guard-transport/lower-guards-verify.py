#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'lower-guards-manifest.json').read_text())
for entry in manifest['entries']:
    path = ROOT / entry['path']
    data = path.read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
selected = ['lower-guards-direct-3', 'lower-guards-canonical-1', 'lower-guards-public-1',
            'lower-guards-kernels-3', 'lower-guards-kernels-public-1']
for stem in selected:
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == 0, stem
    assert json.loads((HERE / receipt['limits']).read_text()) == limits, stem
for receiptPath in HERE.glob('lower-guards-*.json'):
    receipt = json.loads(receiptPath.read_text())
    if 'exit_code' not in receipt:
        continue
    assert json.loads((HERE / receipt['limits']).read_text()) == limits, receiptPath.name
    if 'source' in receipt:
        frozen = HERE / receipt['source']
        assert receipt['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(frozen)], receiptPath.name
        assert hashlib.sha256(frozen.read_bytes()).hexdigest() == receipt['sha256'], receiptPath.name

for stem in ['lower-guards-direct-3', 'lower-guards-kernels-3']:
    assert (HERE / (stem + '.log')).read_bytes() == b'', stem

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
groups = [('lower-guards-public-1', 9), ('lower-guards-kernels-public-1', 1)]
for stem, count in groups:
    source = (HERE / (stem + '.source.lean')).read_text()
    output = (HERE / (stem + '.log')).read_text()
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
    assert len(reports) == count, (stem, len(reports))
    assert {head for head, _ in reports} == set(heads), stem
    for head, axioms in reports:
        plain = re.sub(r'\.\{[^}]*\}', '', axioms)
        names = [name.strip() for name in plain.split(',')]
        assert set(names) <= {'propext', 'Classical.choice', 'Quot.sound'}, (head, names)

production = ROOT / 'lean/MicroCFTA/SourceCurrentLowerGuardHeapReturns.lean'
assert production.read_bytes() == (HERE / 'lower-guards-direct-3.source.lean').read_bytes()
assert hashlib.sha256(production.read_bytes()).hexdigest() == '92c6ae319e1c8ee96c2fa9828e1164ac7d19afd68d484449ae9f0ac2c4a5b6b7'
canonical = (HERE / 'lower-guards-canonical-1.log').read_text()
assert 'Build completed successfully (1786 jobs).' in canonical
assert len(re.findall(r'^warning:', canonical, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in canonical
assert json.loads((HERE / 'lower-guards-direct-1.json').read_text())['exit_code'] != 0
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 9,
                  'constructed_pairs': 1, 'strict_empty': True, 'canonical_jobs': 1786,
                  'old_dependency_warnings': 1, 'actual_memory_cap_bytes': 4294967296,
                  'actual_swap_cap_bytes': 0}))
