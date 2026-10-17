from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'retained-mu-proposal-manifest.json').read_text())
for item in manifest['entries']:
    path = ROOT / item['path']
    data = path.read_bytes()
    assert len(data) == item['bytes'], path
    assert hashlib.sha256(data).hexdigest() == item['sha256'], path
options = [
    'set_option linter.all true', 'set_option pp.explicit true',
    'set_option pp.fullNames true', 'set_option pp.proofs true',
    'set_option pp.universes true', 'set_option pp.deepTerms true',
    'set_option pp.proofs.threshold 254', 'set_option pp.maxSteps 10000000',
]
for stem in manifest['selected_runs']:
    metadata = json.loads((HERE / (stem + '.json')).read_text())
    assert metadata['exit_code'] == 0, stem
    limits = json.loads((HERE / metadata['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    source = (HERE / metadata['source']).read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == metadata['sha256'], stem
    for option in options:
        assert option in source, (stem, option)
    log = (HERE / metadata['log']).read_text()
    assert not re.search(r': (?:error|warning):|sorryAx|failed to pretty print', log), stem
kernel_stem = manifest['kernel_group']['stem']
source = (HERE / (kernel_stem + '.source.lean')).read_text()
log = (HERE / (kernel_stem + '.log')).read_text()
assert re.findall(r'^#check @([^\n]+)$', source, re.M) == manifest['kernel_group']['names']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name in manifest['kernel_group']['names']:
    assert '#print axioms ' + name + '\n' in source, name
    match = re.search(re.escape("'" + name + "' depends on axioms: [") + r'(.*?)\]', log, re.S)
    assert match, name
    axioms = {re.sub(r'\.\{[^}]*\}', '', entry.strip()) for entry in match[1].split(',') if entry.strip()}
    assert axioms <= allowed, (name, axioms)
exploration = (HERE / 'retained-mu-proposal-explore-2.log').read_text()
pattern = r'\((false|true),\s*(false|true),\s*(\d+),\s*(false|true),\s*some \(([^,]+),\s*([^,]+),\s*(\d+),\s*(\d+)\)\)'
rows = re.findall(pattern, exploration)
assert len(rows) == 40, len(rows)
assert len({(used, inner, int(kind)) for used, inner, kind, *_ in rows}) == 40
assert sum(local == 'true' for _, _, _, local, *_ in rows) == 30
for used, inner, kind, local, left, right, middle, after in rows:
    assert left.strip() == right.strip(), (used, inner, kind, left, right)
    assert middle == after, (used, inner, kind, middle, after)
print(f"PASS {len(manifest['entries'])} immutable entries; 40 finite executions (30 used Mu); 2 full-value kernel pairs; caps4G/4G/0; standard axioms")
