import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'recursive-chain-manifest.json').read_text())
for entry in manifest['entries']:
    path = ROOT / entry['path']
    data = path.read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
selected = ['recursive-chain-direct-7', 'recursive-chain-canonical-1',
            'recursive-chain-public-1', 'recursive-chain-kernels-2',
            'recursive-chain-kernels-public-1']
for stem in selected:
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == 0, stem
    assert json.loads((HERE / receipt['limits']).read_text()) == limits, stem
    if 'source' in receipt:
        frozen = HERE / receipt['source']
        assert frozen.is_absolute()
        assert receipt['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(frozen)], stem
        assert hashlib.sha256(frozen.read_bytes()).hexdigest() == receipt['sha256'], stem
for receiptPath in HERE.glob('recursive-chain-*.json'):
    receipt = json.loads(receiptPath.read_text())
    if 'exit_code' not in receipt:
        continue
    assert json.loads((HERE / receipt['limits']).read_text()) == limits, receiptPath.name
    if 'source' in receipt:
        frozen = HERE / receipt['source']
        assert hashlib.sha256(frozen.read_bytes()).hexdigest() == receipt['sha256'], receiptPath.name
        assert receipt['command'][-1] == str(frozen), receiptPath.name

for stem in ['recursive-chain-direct-7', 'recursive-chain-kernels-2']:
    assert (HERE / (stem + '.log')).read_bytes() == b'', stem

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
groups = [('recursive-chain-public-1', 15), ('recursive-chain-kernels-public-1', 2)]
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

production = ROOT / 'lean/MicroCFTA/SourceCurrentRecursiveHeadChainRows.lean'
assert production.read_bytes() == (HERE / 'recursive-chain-direct-7.source.lean').read_bytes()
canonical = (HERE / 'recursive-chain-canonical-1.log').read_text()
assert 'Build completed successfully (1428 jobs).' in canonical
assert len(re.findall(r'^warning:', canonical, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in canonical
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 15,
                  'constructed_pairs': 2, 'strict_empty': True, 'canonical_jobs': 1428,
                  'old_dependency_warnings': 1, 'actual_memory_cap_bytes': 4294967296,
                  'actual_swap_cap_bytes': 0}))
