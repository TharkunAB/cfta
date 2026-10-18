import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((HERE/'node-fusion-review-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT/item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE/'node-fusion-review-selection.json').read_text())
production = ROOT/selection['reviewed_production']
assert sha(production) == selection['sha256']
checker = runpy.run_path(str(HERE/'node-fusion-review-probe-check.py'))
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
strict = json.loads((HERE/(selection['strict']+'.json')).read_text())
assert not (HERE/strict['log']).read_bytes()
assert (HERE/strict['source']).read_bytes() == production.read_bytes()
assert re.findall(r'^theorem (\w+)',production.read_text(),re.M) == ['row','node']
canonical = json.loads((HERE/(selection['canonical']+'.json')).read_text())
log = (HERE/canonical['log']).read_text()
assert 'Build completed successfully (664 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print',log)
kernel = json.loads((HERE/(selection['constructed_strict']+'.json')).read_text())
assert not (HERE/kernel['log']).read_bytes()
assert kernel['sha256'] == 'e837edd5071d8598f8f8454f9db2dc3aa4aaebdfef2900033e394898f508ef99'
s = (HERE/kernel['source']).read_text()
assert 'SourceCurrentFilteredNodeFusion.node' in s
assert 'firstRaw ≠ secondRaw' in s
assert '(nodeEdges firstRaw).length = 3' in s
assert '(nodeEdges output).length = 2' in s
a = s.index('private theorem checked :')+len('private theorem checked :')
b = s.index('theorem changing_reference :')+len('theorem changing_reference :')
assert s[a:s.index(' := by',a)] == s[b:s.index(' := checked',b)]
for extra in selection['additional_modules']:
    path = ROOT/extra['production']
    assert sha(path) == extra['sha256']
    meta = json.loads((HERE/(extra['strict']+'.json')).read_text())
    assert not (HERE/meta['log']).read_bytes()
    assert (HERE/meta['source']).read_bytes() == path.read_bytes()
    canonical = json.loads((HERE/(extra['canonical']+'.json')).read_text())
    log = (HERE/canonical['log']).read_text()
    assert 'Build completed successfully (673 jobs).' in log
    assert not re.search(r'warning:|error:|sorryAx|failed to pretty print',log)
    assert re.findall(r'^theorem (\w+)',path.read_text(),re.M) == ['source']
print(json.dumps({'status':'PASS' ,'files':len(manifest['files']),'new_lean_runs':0,
    'owned_public_pairs':0,'owned_constructed_pairs':0,'reused_public_pairs':3,'reused_constructed_pairs':1,
    'material_issues':0},sort_keys=True))
