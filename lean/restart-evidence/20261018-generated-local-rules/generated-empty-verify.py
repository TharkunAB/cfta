import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE/'generated-empty-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT/item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE/'generated-empty-selection.json').read_text())
checker = runpy.run_path(str(HERE/'generated-empty-probe-check.py'))
for group in selection['groups']+selection['reused_groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE/meta['source']) == meta['sha256'], stem
strict = json.loads((HERE/(selection['strict']+'.json')).read_text())
assert not (HERE/strict['log']).read_bytes()
fixture = HERE/'generated-empty-boundary.lean'
assert fixture.read_bytes() == (HERE/strict['source']).read_bytes()
s = fixture.read_text()
a = s.index('private theorem checked :')+len('private theorem checked :')
b = s.index('theorem witness :')+len('theorem witness :')
assert s[a:s.index(' := by',a)] == s[b:s.index(' := checked',b)]
assert len(re.findall(r'^theorem ',s,re.M)) == 1
public = json.loads((HERE/'generated-empty-boundary-public-1.json').read_text())
assert (HERE/public['source']).read_text().startswith(s)
node = ROOT/'lean/MicroCFTA/SourceCurrentGeneratedNodeCases.lean'
assert sha(node) == selection['reviewed_node_source_sha256']
nodeStrict = json.loads((HERE/'generated-node-direct-4.json').read_text())
assert not (HERE/nodeStrict['log']).read_bytes()
assert node.read_bytes() == (HERE/nodeStrict['source']).read_bytes()
assert selection['production'] is None and selection['canonical'] is None
assert not selection['general_generated_empty_proved']
assert not selection['generated_counterexample_proved']
print(json.dumps({'status':'PASS','files':len(manifest['files']),
    'new_public_pairs':0,'constructed_pairs':1,'auxiliary_pairs':0,'reused_public_pairs':2,
    'strict_log_bytes':0,'general_generated_empty_proved':False,
    'generated_counterexample_proved':False},sort_keys=True))
