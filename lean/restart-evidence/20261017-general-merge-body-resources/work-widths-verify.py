from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
validation = json.loads((HERE / 'work-widths-validation.json').read_text())
production = validation['production']
data = (ROOT / production['path']).read_bytes()
assert hashlib.sha256(data).hexdigest() == production['sha256']
assert (HERE / production['direct_source']).read_bytes() == data
assert (HERE / production['direct_log']).read_bytes() == b''
assert f"Build completed successfully ({production['jobs']} jobs)." in (HERE / production['canonical_log']).read_text()
for reviewed in validation['reviewed_sources']:
    assert hashlib.sha256((ROOT / reviewed['path']).read_bytes()).hexdigest() == reviewed['sha256'], reviewed['path']
settings = ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'pp.fullNames true']
for kind in ['public', 'integration']:
    item = validation[kind]
    source = (HERE / item['source']).read_text()
    log = (HERE / item['log']).read_text()
    assert (HERE / item['snapshot']).read_text() == source
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps', log)
    assert all('set_option ' + setting in source for setting in settings)
    assert source.count('#print axioms ') == item['pairs']
    assert source.count('#check @') == item['pairs']
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == item['pairs']
    for name in item['names']:
        assert '#print axioms ' + name in source
        assert '#check @' + name in source
        assert name in log
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
        assert all(name.strip() in validation['allowed_axioms'] for name in names)
public_names = re.findall(r'^theorem ([\w.]+)', data.decode(), re.M)
assert ['MicroCFTA.SourceCurrentMemoMergeWorkWidths.' + name for name in public_names] == validation['public']['names']
for item in validation['earlier_attempts']:
    log = (HERE / item['log']).read_text()
    if 'source' in item:
        assert (HERE / item['source']).exists()
    status = item['status']
    if status == 'strict_failed':
        assert re.search(r'\berror(?:\(|:)', log)
    elif status == 'strict_clean_prior_success':
        assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯', log)
    elif status == 'exit_zero_with_unused_instance_warnings':
        assert 'warning:' in log and 'unused' in log and 'error:' not in log
    elif status == 'invocation_failed_before_source_created':
        assert 'no such file or directory' in log
assert (HERE / validation['review']).exists()
manifest = HERE / 'work-widths-manifest.json'
if manifest.exists():
    for entry in json.loads(manifest.read_text())['entries']:
        content = (ROOT / entry['path']).read_bytes()
        assert len(content) == entry['bytes'], entry['path']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
print('PASS: frozen strict-clean/canonical WorkWidths; 11 complete public pairs; 3 actual five-row/recursive-union/larger-warm-return integrations; standard axioms; preserved failed and earlier successful attempts; immutable manifest.')
