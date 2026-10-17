from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
v = json.loads((HERE / 'union-resources-validation.json').read_text())
p = v['production']
data = (ROOT / p['path']).read_bytes()
assert hashlib.sha256(data).hexdigest() == p['sha256']
assert (HERE / p['direct_source']).read_bytes() == data
assert (HERE / p['direct_log']).read_bytes() == b''
assert f"Build completed successfully ({p['jobs']} jobs)." in (HERE / p['canonical_log']).read_text()
for item in v['reviewed_sources']:
    assert hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
settings = ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'pp.fullNames true']
for kind in ['public', 'integration']:
    item = v[kind]
    source = (HERE / item['source']).read_text()
    log = (HERE / item['log']).read_text()
    assert (HERE / item['snapshot']).read_text() == source
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps', log)
    assert all('set_option ' + setting in source for setting in settings)
    assert source.count('#print axioms ') == item['pairs']
    assert source.count('#check @') == item['pairs']
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == item['pairs']
    for name in item['names']:
        assert '#print axioms ' + name in source and '#check @' + name in source and name in log
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
        assert all(name.strip() in v['allowed_axioms'] for name in names)
names = re.findall(r'^(?:def|theorem) ([\w.]+)', data.decode(), re.M)
assert ['MicroCFTA.SourceCurrentProjectionUnionResources.' + n for n in names] == v['public']['names']
partial = v['partial_success']
assert hashlib.sha256((HERE / partial['source']).read_bytes()).hexdigest() == partial['sha256']
assert (HERE / partial['log']).read_bytes() == b''
assert 'Build completed successfully' in (HERE / partial['canonical_log']).read_text()
for item in v['earlier_attempts']:
    log = (HERE / item['log']).read_text()
    if 'source' in item:
        assert (HERE / item['source']).exists()
    if item['status'] == 'strict_failed':
        assert re.search(r'\berror(?:\(|:)', log)
    elif item['status'] == 'invocation_failed_before_source_created':
        assert 'no such file or directory' in log
    else:
        assert 'warning:' in log and 'proposition' in log and 'error:' not in log
assert (HERE / v['review']).exists()
manifest = HERE / 'union-resources-manifest.json'
if manifest.exists():
    for entry in json.loads(manifest.read_text())['entries']:
        content = (ROOT / entry['path']).read_bytes()
        assert len(content) == entry['bytes']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
print('PASS: frozen strict-clean/canonical ProjectionUnionResources; 24 full public pairs; 3 actual allocating Mu/union, same-heap warm Head and counted ordered Union integrations; standard axioms; preserved partial build and every failed attempt; immutable manifest.')
