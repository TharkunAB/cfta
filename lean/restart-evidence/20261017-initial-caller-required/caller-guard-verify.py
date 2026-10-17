from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
v = json.loads((HERE / 'caller-guard-validation.json').read_text())
settings = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
            'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
for kind in ['public', 'integration']:
    item = v[kind]
    source = (HERE / item['executed_source']).read_text()
    log = (HERE / item['log']).read_text()
    assert source == (HERE / item['source']).read_text()
    assert all('set_option ' + setting in source for setting in settings)
    assert source.count('#print axioms ') == item['pairs']
    assert source.count('#check @') == item['pairs']
    assert log.count('depends on axioms:') == item['pairs']
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
    for name in item['names']:
        assert '#print axioms ' + name in source and '#check @' + name in source and name in log
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
        assert all(name.strip() in v['allowed_axioms'] for name in names)
for item in [v['fixture'], *v['reviewed_sources']]:
    assert hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
for item in v['canonical']:
    assert f"Build completed successfully ({item['jobs']} jobs)." in (HERE / item['log']).read_text()
for item in v['attempts']:
    assert (HERE / item['source']).exists()
    log = (HERE / item['log']).read_text()
    if item['status'] == 'failed':
        assert 'error:' in log or 'error(' in log
    elif item['status'] == 'fixture_pass_empty':
        assert log == ''
    else:
        assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|declaration uses', log)
source = (HERE / v['integration']['executed_source']).read_text()
assert 'SourceCurrentConstrainedCapClassCallerNumeric.complete 2' in source
assert 'SourceCurrentAllocatedPartialMemoSound.beginNode_sound' in source
assert 'SourceCurrentAllocatedPartialMemoSound.finishEdge_sound' in source
assert '.miss rfl (.open_input' in source
assert 'Context formulas solver inventory (caller width)' in source
for name in ['review', 'inventory', 'headers']:
    assert (HERE / v[name]).exists()
manifest = HERE / 'caller-guard-manifest.json'
if manifest.exists():
    for entry in json.loads(manifest.read_text())['entries']:
        content = (ROOT / entry['path']).read_bytes()
        assert len(content) == entry['bytes'], entry['path']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
print('PASS: initial-only concrete caller ClassPass with derived nonempty phase-sound outer tables and actual warm fourth; public 1 + integration 1 full pairs; standard axioms; exact retained tables/descent; source inventory and immutable attempt hashes match.')
