import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'open-binder-boundary'
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
production = ROOT / selection['production']
assert production.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(production) == selection['sha256']
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (594 jobs).' in log
assert not re.search(r'error:|sorryAx|failed to pretty print',log)
assert re.findall(r'^warning: (.*)$',log,re.M) == [selection['canonical_baseline_warning']]
old = (HERE / (PREFIX + '-direct-8.source.lean')).read_text()
new = production.read_text()
end = '\nend MicroCFTA.SourceCurrentOpenBinderObservationBoundary'
old_decl = old[old.index('theorem arbitrary_reader :'):old.index(end)].strip()
new_decl = new[new.index('private theorem checked_witness :'):new.index('/-- An active open binder can fail',new.index('private theorem checked_witness :'))].strip()
assert old_decl == new_decl.replace('private theorem checked_witness :','theorem arbitrary_reader :',1)
old_statement = old_decl[len('theorem arbitrary_reader :'):old_decl.index(' := by')]
public_decl = new[new.index('theorem arbitrary_reader :'):new.index(end)]
new_statement = public_decl[len('theorem arbitrary_reader :'):public_decl.index(' := checked_witness')]
assert old_statement == new_statement
assert public_decl.strip().endswith(':= checked_witness')
comparison = json.loads((HERE / (PREFIX + '-alias-comparison.json')).read_text())
assert comparison['statement_identical'] is True
assert comparison['exact_statement_sha256'] == hashlib.sha256(old_statement.encode()).hexdigest()
for attempt in selection['retained_unselected']:
    meta = json.loads((HERE / (attempt['stem'] + '.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code'], attempt['stem']
print(json.dumps({'status':'PASS','files':len(manifest['files']),'public_pairs':1,'constructed_pairs':0,'auxiliary_pairs':0,'strict_log_bytes':0,'exact_public_statement_and_private_proof_preserved':True},sort_keys=True))
