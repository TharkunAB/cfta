import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'binder-child-depth-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'binder-child-depth-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'binder-child-depth-probe-check.py'))
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
for stem in [selection['strict'], selection['constructed_strict']]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert (HERE / meta['log']).stat().st_size == 0, stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
production = ROOT / selection['production']
assert production.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(production) == selection['sha256']
assert len(re.findall(r'^theorem ', production.read_text(), re.M)) == 2
assert all(line.rstrip() == line for line in production.read_text().splitlines())
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (271 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
kernel = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
working = HERE / 'binder-child-depth-kernels.lean'
assert working.read_bytes() == (HERE / kernel['source']).read_bytes()
public = json.loads((HERE / (selection['constructed_group'] + '.json')).read_text())
assert (HERE / public['source']).read_text().startswith(working.read_text())
s = working.read_text()
a = s.index('private theorem checked :') + len('private theorem checked :')
b = s.index('theorem constructors :') + len('theorem constructors :')
assert s[a:s.index(' := by', a)] == s[b:s.index(' := checked', b)]
for attempt in selection['retained_unselected']:
    meta = json.loads((HERE / (attempt['stem'] + '.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code'], attempt['stem']
print(json.dumps({'status':'PASS','files':len(manifest['files']),'public_pairs':2,'constructed_pairs':1,'auxiliary_pairs':0,'strict_log_bytes':0,'constructed_strict_log_bytes':0,'exact_public_witness_statement':True}, sort_keys=True))
