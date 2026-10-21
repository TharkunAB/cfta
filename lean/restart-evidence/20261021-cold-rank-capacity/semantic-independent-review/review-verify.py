"""Verify semantic review metadata and the qualified private-instance audit."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--root',type=Path,required=True)
parser.add_argument('--live',action='store_true')
args=parser.parse_args()
load=lambda name:json.loads((HERE/name).read_text())
manifest=load('review-manifest.json');selected=load('review-selection.json')
assert manifest['finalized'] and selected['finalized']
for pin in manifest['files']:
 path=Path(pin['path']);assert not path.is_absolute() and '..' not in path.parts
 data=(HERE/path).read_bytes();assert len(data)==pin['bytes'] and hashlib.sha256(data).hexdigest()==pin['sha256'],str(path)
for name,digest in selected['owner_pins'].items():
 assert hashlib.sha256((HERE/'owner'/name).read_bytes()).hexdigest()==digest,name
index=load('review-source-index.json');owner_index=load('owner/source-index.json')
assert index['all_ranges_reviewed'] and index['sources']==owner_index['sources']
assert len(index['sources'])==20 and sum(len(s['reviewed_ranges']) for s in index['sources'])==24
assert selected['reviewer_lean_jobs']==selected['reviewer_capped_jobs']==selected['reviewer_runtime_jobs']==selected['reviewer_official_edits']==0
assert selected['personally_read_complete_source_and_deltas'] and selected['personally_read_type_lines']==235
assert not selected['personally_read_entire_proof_body'] and selected['authored_foundations_disclosed']
assert not selected['material_issues'] and selected['private_instance_scope_correction_included']
owner_selected=load('owner/cold-rank-semantic-selection.json')
assert owner_selected['source_sha256']==selected['source_sha256']
assert owner_selected['exact_header_sha256']==selected['corrected_header_sha256']
assert owner_selected['actual_lean_jobs']==selected['actual_author_jobs']==2
assert owner_selected['failed_jobs']==owner_selected['warning_bearing_jobs']==0
assert selected['global_root_reported_jobs']==4 and selected['root_audit']=={'jobs':3619,'dependencies':75218}
readback=load('owner/cold-rank-semantic-full-public-readback.json')
assert readback==load('full-readback/independent-reader-result.json')
assert readback['log_bytes']==1330639 and readback['heads'][0]['normalized_type_characters']==11205
assert readback['heads'][0]['body_characters']==1295292
assert readback['heads'][0]['actual_axioms']==['Classical.choice','Quot.sound','propext']
raw=(HERE/'owner/cold-rank-semantic-public-1.log').read_bytes()
type_index=load('owner/public-type-index.json')
checked=(HERE/'owner/cold-rank-semantic-public-type.txt').read_bytes()
assert raw[type_index['start_byte']:type_index['end_byte_exclusive']]==checked
assert checked==(HERE/'full-readback/cold-rank-semantic-public-type.txt').read_bytes()
scope=load('semantic-private-instance-scope-audit.json')
name=scope['imported_private_constant'];printed=checked.decode()
assert printed.count(name)==scope['actual_checked_type_occurrences']==2
assert set(re.findall(r'[\w.]+✝',printed))=={name} and '_private' not in printed
assert scope['broad_private_name_free_claim_withdrawn'] and scope['original_readback_retained']
assert hashlib.sha256((HERE/'owner/cold-rank-semantic-check-full-public.py').read_bytes()).hexdigest()==scope['original_reader_sha256']
assert not re.search(rb'^private\b',(HERE/'owner/SourceCurrentColdRankSemantic.lean').read_bytes(),re.M)
source_pin=next(s for s in index['sources'] if s['path']==scope['definition_root_path'])
assert source_pin['sha256']==scope['definition_complete_source_sha256']
assert hashlib.sha256((HERE/scope['definition_excerpt']).read_bytes()).hexdigest()==scope['definition_excerpt_sha256']
assert selected['no_new_current_module_private_helpers']
command=[sys.executable,str(HERE/'owner/cold-rank-semantic-verify.py'),'--root',str(args.root)]
if args.live:command.append('--live')
result=json.loads(subprocess.check_output(command,text=True,cwd='/'))
assert result['status']=='PASS' and result['local_pins']==selected['owner_local_pins']
assert result['root_pins']==20 and result['source_ranges']==24
assert result['actual_lean_jobs']==2 and result['nonzero_exit_jobs']==0 and result['warning_bearing_jobs']==0
assert result['new_verification_proof_jobs']==0
print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),copied_owner_pins=selected['owner_local_pins'],root_pins=20,source_ranges=24,actual_author_jobs=2,nonzero_author_jobs=0,imported_private_instance_occurrences=2,no_new_current_module_private_helpers=True,reviewer_lean_jobs=0,reviewer_capped_jobs=0,reviewer_runtime_jobs=0),indent=2))
