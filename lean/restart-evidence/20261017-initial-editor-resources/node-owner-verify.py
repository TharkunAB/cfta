from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
v = json.loads((HERE / 'node-owner-validation.json').read_text())
p = v['production']
data = (ROOT / p['path']).read_bytes()
assert hashlib.sha256(data).hexdigest() == p['sha256']
assert (HERE / p['strict_source']).read_bytes() == data
assert (HERE / p['strict_log']).read_bytes() == b''
assert f"Build completed successfully ({p['canonical_jobs']} jobs)." in (HERE / p['canonical_log']).read_text()
exports = ['MicroCFTA.SourceCurrentConstrainedCapEditNumeric.' + n for n in re.findall(r'^theorem ([\w.]+)', data.decode(), re.M)]
assert exports == v['public']['names']
for item in v['reviewed_sources']:
    assert hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
settings = ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'pp.fullNames true']
for kind in ['public', 'integration']:
    item = v[kind]
    source = (HERE / item['source']).read_text()
    log = (HERE / item['log']).read_text()
    assert (HERE / item['snapshot']).read_text() == source
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
    assert all('set_option ' + setting in source for setting in settings)
    assert source.count('#print axioms ') == item['pairs']
    assert source.count('#check @') == item['pairs']
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == item['pairs']
    for name in item['names']:
        assert '#print axioms ' + name in source and '#check @' + name in source and name in log
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
        assert all(name.strip() in v['allowed_axioms'] for name in names)
for item in v['failed_attempts']:
    assert (HERE / item['source']).exists()
    assert 'error:' in (HERE / item['log']).read_text() or 'error(' in (HERE / item['log']).read_text()
assert (HERE / v['review']).exists()
manifest = HERE / 'node-owner-manifest.json'
if manifest.exists():
    for entry in json.loads(manifest.read_text())['entries']:
        content = (ROOT / entry['path']).read_bytes()
        assert len(content) == entry['bytes']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
print('PASS: frozen strict-clean/canonical node producer; 1 public and 1 initial-completion/cap/larger-fuel integration pair; standard axioms; owned production failures preserved; cross-owner collision documented; immutable manifest.')
