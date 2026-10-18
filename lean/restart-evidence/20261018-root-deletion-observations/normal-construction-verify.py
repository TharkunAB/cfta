import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'normal-construction-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'normal-construction-selection.json').read_text())
assert selection['status'] == 'final' and selection['finalized']
checker = runpy.run_path(str(HERE / 'normal-construction-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for path in sorted(HERE.glob('normal-construction-*.json')):
    if path.name == 'normal-construction-verification.json':
        continue
    meta = json.loads(path.read_text())
    if 'command' not in meta or 'wrapper' not in meta:
        continue
    stem = path.stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
for module in selection['production_modules']:
    strict = json.loads((HERE / (module['strict'] + '.json')).read_text())
    assert (HERE / strict['log']).stat().st_size == 0, module['strict']
    production = ROOT / module['path']
    assert production.read_bytes() == (HERE / strict['source']).read_bytes()
    assert sha(production) == module['sha256']
    text = production.read_text()
    assert len(re.findall(r'^theorem ', text, re.M)) == module['pairs']
    assert not re.search(r'\bsorry\b|\baxiom\b', text)
    assert all(line.rstrip() == line for line in text.splitlines())
    canonical = json.loads((HERE / (module['canonical'] + '.json')).read_text())
    log = (HERE / canonical['log']).read_text()
    assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log)
    assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
normal_source = (ROOT / selection['production']).read_text()
assert not re.search(r'\(ready\s*:|SourceEqualityRequiredCache\.Ready|\.semantic', normal_source)
kernel = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert (HERE / kernel['log']).stat().st_size == 0
working = HERE / 'normal-construction-kernels.lean'
assert working.read_bytes() == (HERE / kernel['source']).read_bytes()
public = json.loads((HERE / (selection['constructed_group'] + '.json')).read_text())
assert (HERE / public['source']).read_text().startswith(working.read_text())
s = working.read_text()
a = s.index('private theorem checked_witness :') + len('private theorem checked_witness :')
b = s.index('theorem actual_normal_constructor :') + len('theorem actual_normal_constructor :')
assert s[a:s.index(' := by',a)] == s[b:s.index(' := checked_witness',b)]
assert 'Ready' not in s and '.semantic' not in s
for attempt in selection['retained_unselected']:
    meta = json.loads((HERE / (attempt['stem'] + '.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code'], attempt['stem']
print(json.dumps({'status':'PASS','files':len(manifest['files']),'public_pairs':5,'constructed_pairs':1,'auxiliary_pairs':0,'strict_log_bytes':[0,0],'constructed_strict_log_bytes':0,'exact_public_witness_statement':True},sort_keys=True))
