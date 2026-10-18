import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE/'source-empty-review-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT/item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE/'source-empty-review-selection.json').read_text())
checker = runpy.run_path(str(HERE/'source-empty-review-probes.py'))
for group in selection['reused_groups']:
    checker['check_group'](group)
for stem in manifest['reused_executions']:
    meta = json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code'] == 0
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0]
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE/meta['source']) == meta['sha256']
strict = json.loads((HERE/(selection['strict']+'.json')).read_text())
assert not (HERE/strict['log']).read_bytes()
source = ROOT/selection['production']
assert source.read_bytes() == (HERE/strict['source']).read_bytes()
assert sha(source) == selection['sha256']
assert len(re.findall(r'^theorem ',source.read_text(),re.M)) == 2
canonical = json.loads((HERE/(selection['canonical']+'.json')).read_text())
log = (HERE/canonical['log']).read_text()
assert 'Build completed successfully (267 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print',log)
assert selection['groups'] == []
assert selection['counts']['owned_runs'] == 0
assert not selection['reviewed_constructed_fixture']
print(json.dumps({'status':'PASS','files':len(manifest['files']),
    'owned_runs':0,'new_public_pairs':0,'constructed_pairs':0,'auxiliary_pairs':0,
    'reused_public_pairs':2},sort_keys=True))
