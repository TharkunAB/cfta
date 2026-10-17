from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
m = json.loads((HERE / 'mu-fusion-boundary-manifest.json').read_text())
for item in m['entries']:
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
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
count = 0
for group in m['kernel_groups']:
    stem = group['stem']
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    limits = json.loads((HERE / meta['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    source = (HERE / meta['source']).read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == meta['sha256'], stem
    for option in options:
        assert option in source, (stem, option)
    log = (HERE / meta['log']).read_text()
    assert not re.search(r': (?:error|warning):|sorryAx|failed to pretty print', log), stem
    assert re.findall(r'^#check @([^\n]+)$', source, re.M) == group['names']
    for name in group['names']:
        assert '#print axioms ' + name + '\n' in source, name
        match = re.search(re.escape("'" + name + "' depends on axioms: [") + r'(.*?)\]', log, re.S)
        assert match, name
        axioms = {re.sub(r'\.\{[^}]*\}', '', entry.strip()) for entry in match[1].split(',') if entry.strip()}
        assert axioms <= allowed, (name, axioms)
        count += 1
assert count == 4
for stem, expected in [('mu-fusion-boundary-explore-1',124),('mu-fusion-boundary-stream-1',143),('mu-fusion-boundary-nested-full-1',1)]:
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == expected, stem
print(f"PASS {len(m['entries'])} immutable entries; 4 finite full-Value kernel pairs in 2 groups; standard axioms; caps4G/4G/0; no general fusion claim")
