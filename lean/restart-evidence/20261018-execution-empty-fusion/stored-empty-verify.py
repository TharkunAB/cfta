import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE/'stored-empty-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT/item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE/'stored-empty-selection.json').read_text())
checker = runpy.run_path(str(HERE/'stored-empty-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE/meta['source']) == meta['sha256'], stem
production = ROOT/selection['production']
strict = json.loads((HERE/(selection['strict']+'.json')).read_text())
assert not (HERE/strict['log']).read_bytes()
assert production.read_bytes() == (HERE/strict['source']).read_bytes()
assert sha(production) == selection['sha256']
assert len(re.findall(r'^(?:def|theorem) ',production.read_text(),re.M)) == 5
assert production.read_text().count('[DecidableEq') == 1
canonical = json.loads((HERE/(selection['canonical']+'.json')).read_text())
log = (HERE/canonical['log']).read_text()
assert 'Build completed successfully (554 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print',log)
kernel = json.loads((HERE/(selection['constructed_strict']+'.json')).read_text())
assert not (HERE/kernel['log']).read_bytes()
fixture = HERE/'stored-empty-kernels.lean'
assert fixture.read_bytes() == (HERE/kernel['source']).read_bytes()
s = fixture.read_text()
a = s.index('private theorem checked :')+len('private theorem checked :')
b = s.index('theorem witness :')+len('theorem witness :')
assert s[a:s.index(' := by',a)] == s[b:s.index(' := checked',b)]
assert len(re.findall(r'^theorem ',s,re.M)) == 1
public = json.loads((HERE/'stored-empty-kernels-public-1.json').read_text())
assert (HERE/public['source']).read_text().startswith(s)
assert 'SourceCurrentStoredEmptyInterpreter.execute_test' in s
assert 'SourceCurrentStoredEmptyInterpreter.closed' in s
print(json.dumps({'status':'PASS','files':len(manifest['files']),
    'new_public_pairs':5,'constructed_pairs':1,'auxiliary_pairs':0,
    'production_strict_log_bytes':0,'constructed_strict_log_bytes':0,
    'general_generated_empty_proved':False},sort_keys=True))
