"""Verify immutable Native forwarding sources, capped checks, and complete probe output."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'native-forward-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    data = path.read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

production = ROOT / 'lean/MicroCFTA/SourceCurrentNativeForwardLineage.lean'
strict = json.loads((HERE / 'native-forward-direct-1.json').read_text())
assert strict['exit_code'] == 0
assert (HERE / strict['log']).read_bytes() == b''
assert (HERE / strict['source']).read_bytes() == production.read_bytes()
assert strict['sha256'] == hashlib.sha256(production.read_bytes()).hexdigest()
assert (HERE / 'native-forward-canonical-1.json').exists()
canonical = json.loads((HERE / 'native-forward-canonical-1.json').read_text())
assert canonical['exit_code'] == 0
assert 'Build completed successfully (1171 jobs).' in (HERE / canonical['log']).read_text()

limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for report in sorted(HERE.glob('native-forward-*.json')):
    if '.limits.' in report.name or report.name in {
            'native-forward-manifest.json', 'native-forward-probes.json'}:
        continue
    run = json.loads(report.read_text())
    if 'command' not in run:
        continue
    assert json.loads((HERE / run['limits']).read_text()) == limits, report.name
    if 'source' in run:
        source = HERE / run['source']
        assert hashlib.sha256(source.read_bytes()).hexdigest() == run['sha256'], report.name
        assert run['command'][-1] == str(source), report.name
        assert '-Dlinter.all=true' in run['command'], report.name
    assert (HERE / run['log']).exists(), report.name

options = [
    'set_option linter.all true',
    'set_option pp.explicit true',
    'set_option pp.fullNames true',
    'set_option pp.proofs true',
    'set_option pp.proofs.threshold 254',
    'set_option pp.universes true',
    'set_option pp.deepTerms true',
    'set_option pp.maxSteps 10000000',
]
registry = json.loads((HERE / 'native-forward-probes.json').read_text())
count = 0
for group in registry['groups']:
    source = (ROOT / group['source']).read_text()
    output = (ROOT / group['log']).read_text()
    report = json.loads((ROOT / group['metadata']).read_text())
    assert report['exit_code'] == 0, group['name']
    assert json.loads((ROOT / group['limits']).read_text()) == limits
    assert all(option in source for option in options), group['name']
    assert not re.search(r'warning:|error:|error\(|sorryAx|failed to pretty print|maximum recursion|deterministic timeout|\u22ef|\u2026', output, re.I), group['name']
    assert not re.search(r'\bsorry\b|\baxiom\b|linter\.[\w.]+ false', source), group['name']
    blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    found = dict(blocks)
    assert len(found) == len(blocks) == len(group['names']), group['name']
    assert set(found) == set(group['names']), group['name']
    for name in group['names']:
        assert f'#check @{name}' in source
        assert f'#print {name}\n' in source
        assert f'#print axioms {name}' in source
        assert f'theorem {name}' in output or f'def {name}' in output, name
        normalized = re.sub(r'\.\{[^}]*\}', '', found[name])
        axioms = {part.strip() for part in normalized.split(',')}
        assert axioms == {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    count += len(group['names'])
assert count == 6
assert (HERE / 'native-forward-kernels.lean').read_bytes() == (HERE / 'native-forward-kernels-1.source.lean').read_bytes()
assert (HERE / 'native-forward-public.lean').read_bytes() == (HERE / 'native-forward-public-1.source.lean').read_bytes()
print(f"PASS: {len(manifest['files'])} immutable entries; public 5 + constructed 1; 2 groups; strict log 0 bytes; limits 4 GiB/4 GiB/swap 0; standard axioms only.")
