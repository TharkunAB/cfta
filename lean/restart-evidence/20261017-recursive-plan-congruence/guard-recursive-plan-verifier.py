from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
m = json.loads((HERE / 'guard-recursive-plan-manifest.json').read_text())
for item in m['entries']:
    path = ROOT / item['path']
    data = path.read_bytes()
    assert len(data) == item['bytes'], path
    assert hashlib.sha256(data).hexdigest() == item['sha256'], path
stem = m['selected_group']['stem']
meta = json.loads((HERE / (stem + '.json')).read_text())
assert meta['exit_code'] == 0
assert json.loads((HERE / meta['limits']).read_text()) == {
    'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
source = (HERE / meta['source']).read_text()
assert hashlib.sha256(source.encode()).hexdigest() == meta['sha256']
options = ['set_option linter.all true', 'set_option pp.explicit true',
    'set_option pp.fullNames true', 'set_option pp.proofs true',
    'set_option pp.universes true', 'set_option pp.deepTerms true',
    'set_option pp.proofs.threshold 254', 'set_option pp.maxSteps 10000000']
for option in options:
    assert option in source, option
assert re.findall(r'^#check @([^\n]+)$', source, re.M) == m['selected_group']['names']
log = (HERE / meta['log']).read_text()
assert not re.search(r': (?:error|warning):|sorryAx|failed to pretty print', log)
for name in m['selected_group']['names']:
    assert '#print axioms ' + name + '\n' in source, name
    match = re.search(re.escape("'" + name + "' depends on axioms: [") + r'(.*?)\]', log, re.S)
    assert match, name
    axioms = {re.sub(r'\.\{[^}]*\}', '', part.strip()) for part in match[1].split(',') if part.strip()}
    assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
assert 'SourceCurrentNormalizedPlanCongruence.initial' in source
assert 'captured_recursive_relation seed' in source
assert source.index('theorem captured_recursive_relation') < source.index('SourceCurrentNormalizedPlanCongruence.initial')
print(f"PASS {len(m['entries'])} immutable entries; 1 constructed recursive used-Mu/open-capture pair; standard axioms; caps4G/4G/0")
