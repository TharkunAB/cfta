import hashlib
import json
import re
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'supported-reader-audit'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / (PREFIX + '-selection.json')).read_text())
checker = runpy.run_path(str(HERE / (PREFIX + '-probe-check.py')))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert (HERE / strict['log']).stat().st_size == 0
source = ROOT / selection['production']
assert source.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(source) == selection['sha256']
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (594 jobs).' in log
assert not re.search(r'error:|sorryAx|failed to pretty print',log)
assert re.findall(r'^warning: (.*)$',log,re.M) == [selection['canonical_baseline_warning']]
s = source.read_text()
private_start=s.index('private theorem checked_witness :')+len('private theorem checked_witness :')
private_statement=s[private_start:s.index(' := by',private_start)]
public_start=s.index('theorem arbitrary_reader :')+len('theorem arbitrary_reader :')
public_statement=s[public_start:s.index(' := checked_witness',public_start)]
assert private_statement == public_statement
for attempt in selection['retained_unselected']:
    meta=json.loads((HERE / (attempt['stem'] + '.json')).read_text())
    assert meta['exit_code']==attempt['exit_code'],attempt['stem']
print(json.dumps({'status':'PASS','files':len(manifest['files']),'public_pairs':1,'constructed_pairs':0,'auxiliary_pairs':0,'strict_log_bytes':0,'exact_public_witness_statement':True},sort_keys=True))
