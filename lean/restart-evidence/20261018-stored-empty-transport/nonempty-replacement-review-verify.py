import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'nonempty-replacement-review'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / (PREFIX + '.json')).read_text())
assert selection['status'] == 'final'
assert selection['groups'] == selection['selected_groups'] == []
assert selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == selection['new_lean_runs'] == 0
checker = runpy.run_path(str(HERE / 'generated-growth-probe-check.py'))
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
assert 'Build completed successfully (592 jobs).' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
kernel = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert (HERE / kernel['log']).stat().st_size == 0
working = HERE / 'nonempty-replacement-kernels.lean'
assert working.read_bytes() == (HERE / kernel['source']).read_bytes()
public = json.loads((HERE / (selection['constructed_group'] + '.json')).read_text())
assert (HERE / public['source']).read_text().startswith(working.read_text())
s = working.read_text()
a = s.index('private theorem checked :') + len('private theorem checked :')
b = s.index('theorem witness :') + len('theorem witness :')
assert s[a:s.index(' := by', a)] == s[b:s.index(' := checked', b)]
report = (HERE / selection['report']).read_text()
assert 'No material issue' in report
assert 'physical' in report and 'STORED BODY' in report
print(json.dumps({'status':'PASS','files':len(manifest['files']),'owned_public_pairs':0,'owned_constructed_pairs':0,'reused_public_pairs':2,'reused_constructed_pairs':1,'new_lean_runs':0,'strict_log_bytes':0,'constructed_strict_log_bytes':0,'exact_public_witness_statement':True}, sort_keys=True))
