"""Verify exact outer execution ancestry sources, checked limits, and complete proof probes."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'outer-execution-manifest.json').read_text())
for entry in manifest['files']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

production = ROOT / 'lean/MicroCFTA/SourceCurrentOuterExecutionAncestry.lean'
strict = json.loads((HERE / 'outer-execution-direct-7.json').read_text())
assert strict['exit_code'] == 0
assert (HERE / strict['log']).read_bytes() == b''
assert (HERE / strict['source']).read_bytes() == production.read_bytes()
canonical = json.loads((HERE / 'outer-execution-canonical-1.json').read_text())
assert canonical['exit_code'] == 0
assert 'Build completed successfully (1777 jobs).' in (HERE / canonical['log']).read_text()
assert (HERE / 'outer-execution-kernels-4.log').read_bytes() == b''
assert json.loads((HERE / 'outer-execution-kernels-4.json').read_text())['exit_code'] == 0

limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for metadata in HERE.glob('outer-execution-*.json'):
    report = json.loads(metadata.read_text())
    if 'command' not in report:
        continue
    assert (HERE / report['log']).is_file(), metadata
    assert json.loads((HERE / report['limits']).read_text()) == limits, metadata
    if 'source' in report:
        path = HERE / report['source']
        assert report['sha256'] == hashlib.sha256(path.read_bytes()).hexdigest()
        assert report['command'][-1] == str(path)
        assert '-Dlinter.all=true' in report['command']

options = [
    'set_option linter.all true', 'set_option pp.explicit true',
    'set_option pp.fullNames true', 'set_option pp.proofs true',
    'set_option pp.proofs.threshold 254', 'set_option pp.universes true',
    'set_option pp.deepTerms true', 'set_option pp.maxSteps 10000000',
]
registry = json.loads((HERE / 'outer-execution-probes.json').read_text())
count = 0
for group in registry['groups']:
    source = (ROOT / group['source']).read_text()
    output = (ROOT / group['log']).read_text()
    assert json.loads((ROOT / group['metadata']).read_text())['exit_code'] == 0
    assert json.loads((ROOT / group['limits']).read_text()) == limits
    assert all(option in source for option in options)
    assert not re.search(r'warning:|error:|error\(|sorryAx|failed to pretty print|maximum recursion|deterministic timeout|\u22ef|\u2026', output, re.I)
    assert not re.search(r'\bsorry\b|\baxiom\b|linter\.[\w.]+ false', source)
    records = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))", output)
    found = {name: axioms for name, axioms, _ in records}
    assert len(found) == len(records) == len(group['names'])
    assert set(found) == set(group['names'])
    for name in group['names']:
        assert '#check @' + name + '\n' in source
        assert '#print ' + name + '\n' in source
        assert '#print axioms ' + name + '\n' in source
        assert re.search(r'(?m)^(?:theorem|def|inductive|constructor) ' + re.escape(name) + r'(?:\s|\.|:)', output), name
        axioms = re.sub(r'\.\{[^}]*\}', '', found[name])
        used = {part.strip() for part in axioms.split(',') if part.strip()}
        assert used <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, used)
    count += len(group['names'])
assert count == 25

plain = (HERE / 'outer-execution-kernels-4.source.lean').read_text()
printed = (HERE / 'outer-execution-kernels-public-1.source.lean').read_text()
for name in ['warm_busy_dispatch', 'actual_prefixes']:
    def header(source, name):
        start = source.index('theorem ' + name + ' :')
        return source[start:source.index(' :=', start)]
    assert header(plain, name) == header(printed, name)
assert (HERE / 'outer-execution-public.lean').read_bytes() == (HERE / 'outer-execution-public-1.source.lean').read_bytes()
assert (HERE / 'outer-execution-kernels.lean').read_bytes() == (HERE / 'outer-execution-kernels-4.source.lean').read_bytes()
assert (HERE / 'outer-execution-kernels-public.lean').read_bytes() == (HERE / 'outer-execution-kernels-public-1.source.lean').read_bytes()
print(f'PASS: {len(manifest["files"])} immutable entries; public 13 heads + 10 constructors; constructed 2; full triples 25; strict logs empty; effective 4 GiB/4 GiB/swap 0; standard axioms only.')
