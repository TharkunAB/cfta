#!/usr/bin/env python3
"""Verify the source-only chosen-fuel classification plan without proof commands."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
def digest(data):return hashlib.sha256(data).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');args=p.parse_args()
 manifest=json.loads((HERE/'manifest.json').read_text());assert manifest['finalized'] and manifest['source_only']
 for pin in manifest['files']:
  rel=Path(pin['path']);assert not rel.is_absolute() and '..' not in rel.parts
  data=(HERE/rel).read_bytes();assert len(data)==pin['bytes'] and digest(data)==pin['sha256'],pin['path']
 index=json.loads((HERE/'source-index.json').read_text());assert len(index['sources'])==12 and index['range_count']==12
 for source in index['sources']:
  snapshot=(HERE/source['snapshot']).read_bytes();assert digest(snapshot)==source['sha256']
  lines=snapshot.splitlines(keepends=True)
  for span in source['ranges']:
   block=b''.join(lines[span['start']-1:span['end']]);assert block==(HERE/span['snapshot']).read_bytes() and digest(block)==span['sha256']
  if args.live:assert (args.root/source['live_path']).read_bytes()==snapshot,source['live_path']
 command=[sys.executable,str(HERE/'inputs/local-fault-plan/verify.py'),'--root',str(args.root)]
 if args.live:command.append('--live')
 nested=json.loads(subprocess.check_output(command,cwd='/'));assert nested['status']=='PASS'
 assert digest((HERE/'inputs/local-fault-plan/manifest.json').read_bytes())=='f8f8dabdc527314648dd0da9444ca83b66f0d4e46887f60e7bbaadb9eb39ed35'
 direct_paths={source['live_path']for source in index['sources']}
 old_sources=json.loads((HERE/'inputs/local-fault-plan/source-pins.json').read_text())['sources'];paths=direct_paths|{source['path']for source in old_sources};assert len(paths)==17
 selection=json.loads((HERE/'selection.json').read_text());assert selection['finalized'] and selection['source_only']
 for field in ['lean_jobs','lake_jobs','canonical_jobs','runtime_jobs','public_pairs','constructed_pairs','official_edits']:assert selection[field]==0
 assert selection['selected_attempts']==[] and selection['proposed_public_heads']==['done_or_exhausted']
 for name,sha,lines in [('plan.md','dd47341cc968bd45abfe46f8a4f9b57e6b298317115ce21269d62da9b31c1b58',34),('proposed-signature.lean.txt','1c55624f7acb80c07d68b0c1cdca5d6d12498f28e9294f693f655a541e81c304',34),('proposed-context.lean.txt','605eb3526069dd4ce0a7290a15bc208c4e2458087d94d187d2c582b30baf9cc7',21)]:
  data=(HERE/name).read_bytes();assert digest(data)==sha and len(data.splitlines())==lines
 before=(HERE/'plan-before-dependency-status.md').read_text();assert digest(before.encode())=='c1d85c833eba07cc5b3f9690f809de7c50a32e9c5926079dbe32f26b68af5cf9'
 expected=before.replace('Dependency: SourceCurrentOuterLocalFaults.failed_cases remains an unimplemented, unproved21-line proposal. Its frozen plan is retained unchanged.','Dependency: SourceCurrentOuterLocalFaults.failed_cases remains an unchecked21-line public proposal. Its frozen plan is retained unchanged. A separate source-only implementation draft is under review; no checked declaration is available.')
 assert expected==(HERE/'plan.md').read_text()
 scope=json.loads((HERE/'scope.json').read_text());assert scope['total_source_hard_stop']==150 and scope['stop_before']==['compiler','further_implementation']
 assert scope['whole_source_review_required']==['root','guard_inventory'] and scope['official_compiled_LocalFaults_required'] and scope['separate_root_activation_required']
 assert not scope['implementation_authorized'] and not scope['compiler_authorized'] and scope['original_estimate_is_not_permission']
 dependency=json.loads((HERE/'dependency-status.json').read_text());assert dependency['LocalFaults']['status']=='unchecked_source_only_public_contract' and not dependency['new_declaration_implemented'] and dependency['actual_proof_jobs']==0
 assert not list(HERE.glob('*.lean')) and not list(HERE.glob('*.olean')) and not list(HERE.glob('*.log'))
 print(json.dumps({'status':'PASS','live':args.live,'source_only':True,'local_pins':len(manifest['files']),'root_pins':len(paths),'direct_source_pins':12,'direct_source_ranges':12,'historical_source_ranges':17,'proposed_public_heads':['done_or_exhausted'],'lean_jobs':0,'lake_jobs':0,'canonical_jobs':0,'runtime_jobs':0,'public_pairs':0,'constructed_pairs':0,'official_edits':0,'total_source_hard_stop':150,'LocalFaults_unchecked_at_cue':True,'adequate_fuel_and_joint_Room_unproved':True,'completion_proved':False,'manifest_sha256':digest((HERE/'manifest.json').read_bytes())},indent=2))
if __name__=='__main__':main()
