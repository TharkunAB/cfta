import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'generated-union-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'generated-union-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'generated-union-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert (HERE / strict['log']).stat().st_size == 0
source = ROOT / selection['production']
assert source.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(source) == selection['sha256']
assert len(re.findall(r'^theorem ', source.read_text(), re.M)) == 3
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (609 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
kernel = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert (HERE / kernel['log']).stat().st_size == 0
working = HERE / 'generated-union-kernels.lean'
assert working.read_bytes() == (HERE / kernel['source']).read_bytes()
public = json.loads((HERE / (selection['constructed_group'] + '.json')).read_text())
assert (HERE / public['source']).read_text().startswith(working.read_text())
s = working.read_text()
a = s.index('private theorem checked_witness :') + len('private theorem checked_witness :')
b = s.index('theorem warm_parent_cold_subgroup :') + len('theorem warm_parent_cold_subgroup :')
assert s[a:s.index(' := by', a)] == s[b:s.index(' := checked_witness', b)]
assert len(re.findall(r'^theorem ', s, re.M)) == 1
print(json.dumps({'status':'PASS','files':len(manifest['files']),'public_pairs':3,'constructed_pairs':1,'auxiliary_pairs':0,'strict_log_bytes':0,'constructed_strict_log_bytes':0,'exact_public_witness_statement':True}, sort_keys=True))
