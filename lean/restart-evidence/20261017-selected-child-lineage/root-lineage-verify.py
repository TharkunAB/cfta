import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'root-lineage-manifest.json').read_text())
for entry in manifest['entries']:
 assert sha(ROOT/entry['path'])==entry['sha256'],entry['path']
checks=runpy.run_path(str(HERE/'verify-probes.py'))
for stem,count in [('selected-child-public-1',4),('reader-row-public-1',2)]:
 checks['check_group']({'name':stem,'pairs':count,'full_proof':True})
for module,stem in [('SourceCurrentSharedEditChildLineage','selected-child-direct-5'),('SourceCurrentNativeReaderRowLineage','reader-row-direct-2')]:
 meta=json.loads((HERE/(stem+'.json')).read_text())
 assert meta['exit_code']==0 and not (HERE/meta['log']).read_bytes()
 assert sha(HERE/meta['source'])==sha(ROOT/'lean/MicroCFTA'/(module+'.lean'))
 checks['check_limits'](stem)
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'public_pairs':6,'full_public_proof_output':True,'strict_empty_modules':2,'general_outer_progress_still_open':True}))
