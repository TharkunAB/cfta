"""Verify cold proof review metadata without compiling or evaluating C."""
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
assert len(index['sources'])==21 and sum(len(s['reviewed_ranges']) for s in index['sources'])==26
assert all(s['authority']=='root' for s in index['sources'])
assert selected['reviewer_lean_jobs']==selected['reviewer_capped_jobs']==selected['reviewer_runtime_jobs']==selected['reviewer_official_edits']==0
assert selected['personally_read_complete_source_and_deltas'] and selected['personally_read_type_lines']==194
assert not selected['personally_read_entire_proof_body'] and selected['authored_foundations_disclosed']
assert not selected['material_issues']
owner_selected=load('owner/cold-rank-capacity-selection.json')
assert owner_selected['source_sha256']==selected['source_sha256']
assert owner_selected['exact_header_sha256']==selected['corrected_header_sha256']
assert owner_selected['actual_lean_jobs']==selected['actual_author_jobs']==4
assert owner_selected['failed_jobs']==selected['nonzero_author_jobs']==1
assert owner_selected['warned_zero_exit_jobs']==1 and owner_selected['clean_zero_exit_jobs']==2
assert selected['global_root_reported_jobs']==6 and selected['root_audit']=={'jobs':3618,'dependencies':75217}
readback=load('owner/cold-rank-capacity-full-public-readback.json')
assert readback==load('full-readback/cold-rank-capacity-full-public-readback.json')
assert readback['log_bytes']==365789 and readback['heads'][0]['normalized_type_characters']==9259
assert readback['heads'][0]['body_characters']==337314
assert readback['heads'][0]['actual_axioms']==['Classical.choice','Quot.sound','propext']
raw=(HERE/'owner/cold-rank-capacity-public-1.log').read_text()
head='MicroCFTA.SourceCurrentColdRankCapacity.constructed_initial_node_call'
match=re.search(r'^(?:@)?'+re.escape(head)+r' :',raw,re.M);assert match
end=raw.index('\ntheorem '+head+' :',match.end())
assert raw[match.end():end].encode()==(HERE/'owner/cold-rank-capacity-public-TYPE.lean.txt').read_bytes()
assert (HERE/'owner/cold-rank-capacity-public-TYPE.lean.txt').read_bytes()==(HERE/'full-readback/cold-rank-capacity-public-TYPE.lean.txt').read_bytes()
command=[sys.executable,str(HERE/'owner/cold-rank-capacity-verify.py'),'--root',str(args.root)]
if args.live:command.append('--live')
result=json.loads(subprocess.check_output(command,text=True,cwd='/'))
assert result['status']=='PASS' and result['local_pins']==176 and result['root_pins']==21 and result['source_ranges']==26
assert result['actual_lean_jobs']==4 and result['nonzero_exit_jobs']==1 and result['warned_zero_exit_jobs']==1 and result['clean_zero_exit_jobs']==2
assert result['new_verification_proof_jobs']==0
print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),copied_owner_pins=176,root_pins=21,source_ranges=26,actual_author_jobs=4,nonzero_author_jobs=1,warned_zero_author_jobs=1,clean_zero_author_jobs=2,reviewer_lean_jobs=0,reviewer_capped_jobs=0,reviewer_runtime_jobs=0),indent=2))
