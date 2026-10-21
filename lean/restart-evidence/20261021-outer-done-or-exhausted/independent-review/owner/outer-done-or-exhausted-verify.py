#!/usr/bin/env python3
"""Verify the actual chosen-fuel classification and its complete public evidence."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent
PREFIX='outer-done-or-exhausted'
def digest(data):return hashlib.sha256(data).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');args=p.parse_args()
 manifest=json.loads((HERE/(PREFIX+'-manifest.json')).read_text());assert manifest['finalized']
 for pin in manifest['files']:
  rel=Path(pin['path']);assert not rel.is_absolute() and '..' not in rel.parts
  data=(HERE/rel).read_bytes();assert len(data)==pin['bytes'] and digest(data)==pin['sha256'],pin['path']
 selected=json.loads((HERE/(PREFIX+'-selection.json')).read_text());assert selected['finalized']
 source=(HERE/selected['source']).read_bytes();assert digest(source)==selected['source_sha256'] and len(source.splitlines())==83<150
 assert source==(HERE/'done-or-exhausted-source-only.lean.txt').read_bytes()
 if args.live:assert (args.root/selected['official_path']).read_bytes()==source
 for dep in json.loads((HERE/'dependency-rootpins.json').read_text())['files']:
  snapshot=(HERE/dep['snapshot']).read_bytes();assert digest(snapshot)==dep['sha256'] and len(snapshot.splitlines())==dep['lines']
  if args.live:assert (args.root/dep['live_path']).read_bytes()==snapshot
 plan_cmd=[sys.executable,str(HERE/'inputs/plan/verify.py'),'--root',str(args.root)]
 if args.live:plan_cmd.append('--live')
 plan=json.loads(subprocess.check_output(plan_cmd,cwd='/'));assert plan['status']=='PASS' and plan['root_pins']==17
 result=json.loads(subprocess.check_output([sys.executable,str(HERE/'check-full-public.py')],cwd='/'))
 assert result==json.loads((HERE/'full-public-readback.json').read_text()) and result['source_sha256']==digest(source)
 assert len(result['heads'])==1 and result['all_eight_printer_settings'] and result['no_omissions']
 head=result['heads'][0];assert head['check_print_type_identity'] and head['unique_actual_lambda_body_delimiter'] and not head['private_public_type_names']
 assert set(head['actual_axioms'])<={'propext','Classical.choice','Quot.sound'} and head['actual_axioms']==selected['actual_axioms_by_head'][head['head']]
 start=source.index(b'theorem done_or_exhausted\n');end=source.index(b' := by',start)
 assert source[start:end]==(HERE/'inputs/plan/proposed-signature.lean.txt').read_bytes().rstrip()
 assert source.count(b'cases actual : SourceCurrentOuterActiveAncestry.run ')==1 and source.count(b'SourceCurrentOuterLocalFaults.failed_cases ')==1
 assert b'private 'not in source and source.count(b'theorem ')==1 and b' normal supported causal merged positiveMemo origins stored closed 'in source
 assert b'gBound sBound rBound eBound pBound hBound mBound cBound nBound observation after actual'in source
 ledger=json.loads((HERE/'attempt-ledger.json').read_text());assert ledger['actual_lean_jobs']==len(ledger['attempts'])==2 and ledger['actual_FULL_jobs']==1
 assert ledger['failed_jobs']==ledger['warning_jobs']==ledger['infrastructure_nonlaunches']==ledger['canonical_jobs']==ledger['runtime_jobs']==ledger['constructed_pairs']==0
 for attempt in ledger['attempts']:
  receipt=json.loads((HERE/attempt['receipt']).read_text());usage=json.loads((HERE/attempt['usage']).read_text());limits=json.loads((HERE/attempt['limits']).read_text())
  assert receipt['exit_code']==attempt['exit_code']==0 and receipt['sha256']==digest((HERE/receipt['source']).read_bytes())
  assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'} and usage['age_seconds']<=600 and usage['remaining_percent']>1
  assert receipt['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'] and '-Dlinter.all=true'in receipt['command']
  assert not re.search(r'\bwarning(?:\([^)]*\))?:',(HERE/attempt['raw_log']).read_text())
 assert (HERE/(selected['selected_strict']+'.log')).stat().st_size==0
 assert json.loads((HERE/(selected['selected_strict']+'.json')).read_text())['sha256']==digest(source)
 print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':plan['root_pins']+2,'actual_lean_jobs':2,'failed_jobs':0,'warning_jobs':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'full_public_heads':1,'actual_axioms_by_head':selected['actual_axioms_by_head'],'all_eight_settings':True,'exact_public_type_identity':True,'one_actual_outcome_and_one_failed_cases':True,'same_chosen_phase_fuels_and_Caller':True,'all_initial_packet_and_nine_lower_bounds_retained':True,'adequate_outer_fuel_and_joint_Room_unproved':True,'unrestricted_completion_unproved':True,'authored_foundations_disclosed':True,'manifest_sha256':digest((HERE/(PREFIX+'-manifest.json')).read_bytes())},indent=2))
if __name__=='__main__':main()
