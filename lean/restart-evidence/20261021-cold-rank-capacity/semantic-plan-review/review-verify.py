"""Verify source-plan review metadata without compiling or evaluating C."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
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
 data=(HERE/path).read_bytes();assert len(data)==pin['bytes'] and hashlib.sha256(data).hexdigest()==pin['sha256']
index=load('review-source-index.json');owner=load('owner/source-index.json')
assert index['all_ranges_reviewed'] and index['sources']==owner['sources']
assert len(index['sources'])==17 and sum(len(s['reviewed_ranges']) for s in index['sources'])==20
assert selected['source_only'] and not selected['semantic_corollary_proved']
assert selected['reviewer_proof_jobs']==selected['reviewer_capped_jobs']==selected['reviewer_runtime_jobs']==0
assert hashlib.sha256((HERE/'owner/manifest.json').read_bytes()).hexdigest()==selected['owner_manifest_sha256']
assert hashlib.sha256((HERE/'owner/selection.json').read_bytes()).hexdigest()==selected['owner_selection_sha256']
command=[sys.executable,str(HERE/'owner/verify.py'),'--root',str(args.root)]
if args.live: command.append('--live')
result=json.loads(subprocess.check_output(command,text=True,cwd='/'))
assert result['status']=='PASS' and result['local_pins']==57 and result['root_pins']==17 and result['source_ranges']==20
assert result['new_lean_jobs']==result['new_runtime_jobs']==0
print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),root_pins=17,source_ranges=20,reviewer_proof_jobs=0,reviewer_runtime_jobs=0),indent=2))
