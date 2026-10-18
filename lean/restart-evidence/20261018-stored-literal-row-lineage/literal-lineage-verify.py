import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
checks=runpy.run_path(str(HERE/'verify-probes.py'))
manifest=json.loads((HERE/'literal-lineage-manifest.json').read_text())
for entry in manifest['entries']:
 path=ROOT/entry['path']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'],entry['path']
 assert path.stat().st_size==entry['bytes'],entry['path']
selection=json.loads((HERE/'literal-lineage-selection.json').read_text())
module=ROOT/'lean/MicroCFTA/SourceCurrentStoredLiteralRowLineage.lean'
strict=json.loads((HERE/(selection['strict']+'.json')).read_text())
assert strict['exit_code']==0 and not (HERE/strict['log']).read_bytes()
assert checks['sha'](HERE/strict['source'])==checks['sha'](module)==selection['source_sha256']
checks['check_limits'](selection['strict'])
canonical=json.loads((HERE/(selection['canonical']+'.json')).read_text())
log=(HERE/canonical['log']).read_text()
assert canonical['exit_code']==0 and 'Build completed successfully' in log
assert not re.search(r'^warning:',log,re.M)
checks['check_limits'](selection['canonical'])
for group in selection['groups']:checks['check_group'](group)
print(json.dumps({'status':'PASS','manifest_entries':len(manifest['entries']),'production_public_pairs':8,'strict_empty_logs':1,'full_proofs_standard_axioms':True,'source_sha256':checks['sha'](module)},indent=2))
