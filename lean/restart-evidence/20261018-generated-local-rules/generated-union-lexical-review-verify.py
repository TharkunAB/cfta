import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'generated-union-lexical-review-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'generated-union-lexical-review-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'generated-union-probe-check.py'))
for group in selection['reviewed_groups']:
    checker['check_group'](group)
for stem in [selection['strict'], selection['canonical'], 'lexical-public-1']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
source = ROOT / selection['production']
assert sha(source) == selection['sha256']
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert (HERE / strict['log']).stat().st_size == 0
assert source.read_bytes() == (HERE / strict['source']).read_bytes()
assert len(re.findall(r'^theorem ', source.read_text(), re.M)) == 2
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (600 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
assert selection['selected_groups'] == selection['groups'] == []
print(json.dumps({'status':'PASS','files':len(manifest['files']),'new_public_pairs':0,'new_constructed_pairs':0,'new_auxiliary_pairs':0,'reused_public_pairs':2,'strict_log_bytes':0}, sort_keys=True))
