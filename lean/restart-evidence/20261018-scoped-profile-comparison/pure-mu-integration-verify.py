import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((HERE/'pure-mu-integration-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT/item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE/'pure-mu-integration-selection.json').read_text())
checker = runpy.run_path(str(HERE/'pure-mu-integration-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    assert sha(HERE/meta['source']) == meta['sha256'], stem
strict = json.loads((HERE/(selection['strict']+'.json')).read_text())
assert (HERE/strict['log']).stat().st_size == 0
source = HERE/selection['working_source']
assert source.read_bytes() == (HERE/strict['source']).read_bytes()
assert sha(source) == selection['sha256']
s = source.read_text()
a = s.index('private theorem checked :') + len('private theorem checked :')
b = s.index('theorem actual_open :') + len('theorem actual_open :')
assert s[a:s.index(' := by',a)] == s[b:s.index(' := checked',b)]
assert len(re.findall(r'^theorem ',s,re.M)) == 1
assert all(line.rstrip() == line for line in s.splitlines())
assert 'SourceCurrentStoredProfileFunction.congr body' in s
for name in ['recapture','rebind']:
    assert 'SourceCurrentStoredProfilePlan.'+name in s
for name in ['fresh_marker','open_denote','open_correct']:
    assert 'SourceCurrentStoredMuProfileReduction.'+name in s
assert '.binder false (.binder false (.binder false (.var 2)))' in s
public = json.loads((HERE/(selection['constructed_group']+'.json')).read_text())
assert (HERE/public['source']).read_text().startswith(s)
for attempt in selection['retained_unselected']:
    meta = json.loads((HERE/(attempt['stem']+'.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code']
print(json.dumps({'status':'PASS','files':len(manifest['files']),'public_pairs':0,'constructed_pairs':1,'auxiliary_pairs':0,'strict_log_bytes':0,'exact_public_witness_statement':True},sort_keys=True))
