import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'binder-plan-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'binder-plan-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'binder-plan-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
production = ROOT / selection['production']
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert not (HERE / strict['log']).read_bytes()
assert production.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(production) == selection['sha256']
assert re.findall(r'^theorem (\w+)', production.read_text(), re.M) == ['rebind_profile', 'open_execute']
assert not re.findall(r'^def (\w+)', production.read_text(), re.M)
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
kernel = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert not (HERE / kernel['log']).read_bytes()
fixture = HERE / 'binder-plan-kernels.lean'
assert fixture.read_bytes() == (HERE / kernel['source']).read_bytes()
source = fixture.read_text()
start = source.index('private theorem checked :') + len('private theorem checked :')
public = source.index('theorem witness :') + len('theorem witness :')
assert source[start:source.index(' := by', start)] == source[public:source.index(' := checked', public)]
assert len(re.findall(r'^theorem ', source, re.M)) == 1
assert 'SourceCurrentStoredMuEmptyPlan.rebind_profile' in source
assert 'SourceCurrentStoredMuEmptyPlan.open_execute' in source
assert 'SourceEqualityRequiredCache.constructed' in source
assert '.binder false (.binder false (.binder false (.union [.var 1,.var 2])))' in source
assert 'execute target environment reader = .done .empty after' in source
assert 'unlowered = some [Sum.inl ()]' in source
assert 'isEmpty unlowered = false' in source
assert 'isEmpty (lower unlowered) = true' in source
printed = json.loads((HERE / 'binder-plan-kernels-public-1.json').read_text())
assert (HERE / printed['source']).read_text().startswith(source)
print(json.dumps(dict(status='PASS', files=len(manifest['files']), new_public_pairs=2,
    constructed_pairs=1, auxiliary_pairs=0, production_strict_log_bytes=0,
    constructed_strict_log_bytes=0, same_body_symbolic_rebinding=True,
    actual_open_mu_empty_with_lower=True, writer_ordinary_probe_comparison_proved=False), sort_keys=True))
