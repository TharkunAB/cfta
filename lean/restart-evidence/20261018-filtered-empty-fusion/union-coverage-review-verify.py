import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'union-coverage-review-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'union-coverage-review.json').read_text())
assert selection['status'] == 'final'
assert selection['groups'] == selection['selected_groups'] == []
assert selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == selection['new_lean_runs'] == 0
checker = runpy.run_path(str(HERE / 'node-empty-probe-check.py'))
for group in selection['reused_groups']:
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
assert len(re.findall(r'^theorem ', source.read_text(), re.M)) == 2
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (612 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
report = (HERE / selection['report']).read_text()
assert 'No material issue' in report
assert 'bare-self' in report and 'complete ordinary rows' in report
print(json.dumps({'status':'PASS','files':len(manifest['files']),'owned_public_pairs':0,'owned_constructed_pairs':0,'reused_public_pairs':2,'reused_constructed_pairs':0,'new_lean_runs':0,'strict_log_bytes':0}, sort_keys=True))
