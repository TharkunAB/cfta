import hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE.parents[2]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'rooted-writers-source-pins.json').read_text())
assert manifest['status']=='final'
for entry in manifest['files']:
 path=ROOT/entry['path']
 assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],entry['path']
for entry in manifest['review_files']:
 path=HERE/entry['path']
 assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],entry['path']
selection=json.loads((HERE/'rooted-writers-review-selection.json').read_text())
assert selection['owned_lean_jobs']==selection['owned_public_pairs']==selection['owned_constructed_pairs']==0
assert len(selection['independent_review'])==len(selection['author_reread'])==1
assert len(selection['independent_review'][0]['public_declarations'])==3
assert len(selection['author_reread'][0]['public_declarations'])==2
print(json.dumps({'status':'PASS','scope':'Pinned mathematical source review only; no new Lean run.','source_pins':len(manifest['files']),'owned_review_pins':len(manifest['review_files']),'independent_rooted_declarations':3,'capture_author_reread_declarations':2,'owned_lean_jobs':0,'owned_pairs':0,'manifest_sha256':sha(HERE/'rooted-writers-source-pins.json')},indent=2))
