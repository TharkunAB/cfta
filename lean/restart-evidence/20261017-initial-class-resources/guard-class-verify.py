from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
v = json.loads((HERE / 'guard-class-validation.json').read_text())
source = (HERE / v['executed_source']).read_text()
log = (HERE / v['log']).read_text()
assert source == (HERE / v['live_source']).read_text()
settings = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
            'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
assert all('set_option ' + setting in source for setting in settings)
assert source.count('#print axioms ') == v['pairs']
assert source.count('#check @') == v['pairs']
assert log.count('depends on axioms:') == v['pairs']
assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
for name in v['names']:
    assert '#print axioms ' + name in source
    assert '#check @' + name in source
    assert name in log
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
    names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
    assert all(name.strip() in v['allowed_axioms'] for name in names)
for item in [v['source_fixture'], *v['reviewed_sources']]:
    assert hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
for item in v['canonical']:
    assert f"Build completed successfully ({item['jobs']} jobs)." in (HERE / item['log']).read_text()
for item in v['attempts']:
    attempt = (HERE / item['source']).read_text()
    output = (HERE / item['log']).read_text()
    if item['status'] == 'failed':
        assert 'error:' in output
    elif item['status'] == 'fixture_pass_empty':
        assert output == ''
    else:
        assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|declaration uses', output)
assert 'SourceCurrentConstrainedCapClassNumeric.complete 2' in source
assert 'SourceCurrentConstrainedCapClassPassNumeric.pass 2' in source
assert 'selectedRecord, selectedRecord' in source
assert 'results = EqualityLeafProjectionRuntimeEmpty.propagate raw' in source
assert 'HEq actual' in source
assert (HERE / v['review']).exists()
manifest = HERE / 'guard-class-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    for entry in entries:
        content = (ROOT / entry['path']).read_bytes()
        assert len(content) == entry['bytes'], entry['path']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
print('PASS: initial-only concrete open constrained Class and exact two-Class Pass; 2 full axiom/signature pairs; standard axioms; all 5 current-prefix attempt snapshots/logs retained; immutable hashes match.')
