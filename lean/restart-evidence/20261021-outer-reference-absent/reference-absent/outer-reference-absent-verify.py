#!/usr/bin/env python3
"""Verify the two literal outer fault exclusions and their preserved evidence."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent
PREFIX='outer-reference-absent'
def digest(data):return hashlib.sha256(data).hexdigest()
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True);parser.add_argument('--live',action='store_true');args=parser.parse_args()
 manifest=json.loads((HERE/(PREFIX+'-manifest.json')).read_text());assert manifest['finalized']
 for pin in manifest['files']:
  data=(HERE/pin['path']).read_bytes();assert len(data)==pin['bytes'] and digest(data)==pin['sha256'],pin['path']
 selected=json.loads((HERE/(PREFIX+'-selection.json')).read_text());assert selected['finalized']
 source=(HERE/selected['source']).read_bytes();assert digest(source)==selected['source_sha256'] and len(source.splitlines())==254
 if args.live:assert (args.root/selected['official_path']).read_bytes()==source
 for dep in json.loads((HERE/'dependency-rootpins.json').read_text())['files']:
  snapshot=(HERE/dep['snapshot']).read_bytes();assert digest(snapshot)==dep['sha256'] and len(snapshot.splitlines())==dep['lines']
  if args.live:assert (args.root/dep['live_path']).read_bytes()==snapshot
 plan_cmd=[sys.executable,str(HERE/'inputs/plan/verify.py'),'--root',str(args.root)]
 if args.live:plan_cmd.append('--live')
 plan=json.loads(subprocess.check_output(plan_cmd,cwd='/'));assert plan['status']=='PASS'
 result=json.loads(subprocess.check_output([sys.executable,str(HERE/'check-full-public.py')],cwd='/'))
 assert result==json.loads((HERE/'full-public-readback.json').read_text()) and result['source_sha256']==digest(source)
 assert len(result['heads'])==1 and result['all_eight_printer_settings'] and result['no_omissions']
 head=result['heads'][0];assert head['check_print_type_identity'] and head['unique_actual_lambda_body_delimiter'] and not head['private_public_type_names']
 assert set(head['actual_axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert head['actual_axioms']==selected['actual_axioms_by_head'][head['head']]
 proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_bytes().rstrip()
 start=source.index(b'theorem no_reference_or_node_absent\n');end=source.index(b' := by',start);assert source[start:end]==proposal
 original=(HERE/'reference-absent-prelaunch-254.lean.txt').read_text()
 assert digest(original.encode())=='48c8a6a093489ae2376ab45c995691de9a751af5de52f558ee8b3fafce52099f'
 assert digest((HERE/'write-source.py').read_bytes())=='827d6ee20ce494b684184d4834abd013c226f24a4b29025ed30db7a2a5b1cf79'
 selector=original
 for worker in ['walk','rows','nodeBody']:
  old=f'| zero => simp only [{worker}] at failed; cases failed';new=f'| zero => simp only [{worker}] at failed; cases kind <;> simp only [diagnostic] at failed <;> cases failed'
  assert selector.count(old)==1;selector=selector.replace(old,new)
 old='      split at failed\n      · cases failed\n      · cases failed\n      · rename_i combined observed'
 new='      split at failed\n      · cases kind <;> simp only [diagnostic] at failed <;> cases failed\n      · cases kind <;> simp only [diagnostic] at failed <;> cases failed\n      · rename_i combined observed'
 assert selector.count(old)==1;selector=selector.replace(old,new)
 for kind in ['true','false']:
  old=f'failure_cut (kind := {kind}) failed';assert selector.count(old)==1
  selector=selector.replace(old,f'failure_cut (kind := {kind}) (name := name) (handle := handle) failed')
 assert selector.encode()==(HERE/(PREFIX+'-direct-1.source.lean')).read_bytes()
 old='| rows fuel inherited values before => exact (all_failures fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)'
 new='| rows fuel inherited values before => exact (all_failures fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)'
 assert selector.count(old)==1 and selector.replace(old,new).encode()==source
 ledger=json.loads((HERE/'attempt-ledger.json').read_text())
 assert ledger['actual_lean_jobs']==len(ledger['attempts'])==3 and ledger['failed_jobs']==1 and ledger['actual_FULL_jobs']==1
 assert ledger['warning_jobs']==ledger['infrastructure_nonlaunches']==ledger['canonical_jobs']==ledger['runtime_jobs']==ledger['constructed_pairs']==0
 assert [a['exit_code']for a in ledger['attempts']]==[1,0,0]
 for attempt in ledger['attempts']:
  receipt=json.loads((HERE/attempt['receipt']).read_text());usage=json.loads((HERE/attempt['usage']).read_text());limits=json.loads((HERE/attempt['limits']).read_text())
  assert receipt['exit_code']==attempt['exit_code'] and receipt['sha256']==digest((HERE/receipt['source']).read_bytes())
  assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'} and usage['age_seconds']<=600 and usage['remaining_percent']>1
  assert receipt['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'] and '-Dlinter.all=true' in receipt['command']
  assert not re.search(r'\bwarning(?:\([^)]*\))?:',(HERE/attempt['raw_log']).read_text())
 failed=(HERE/(PREFIX+'-direct-1.log')).read_text();assert len(failed.encode())==558 and failed.count('error:')==1
 assert (HERE/(selected['selected_strict']+'.log')).stat().st_size==0
 assert json.loads((HERE/(selected['selected_strict']+'.json')).read_text())['sha256']==digest(source)
 assert source.count(b'SourceCurrentOuterClosedInputs.reached ')==1 and source.count(b'actual.valid valid')==1
 print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':plan['root_pins']+2,'actual_lean_jobs':3,'failed_jobs':1,'warning_jobs':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'full_public_heads':1,'actual_axioms_by_head':selected['actual_axioms_by_head'],'all_eight_settings':True,'exact_public_type_identity':True,'same_failed_caller_and_actual_cuts':True,'four_line_scope_overflow_disclosed':True,'explicit_254_source_exception':True,'only_two_faults':True,'adequate_fuel_and_completion_unproved':True,'authored_foundations_disclosed':True,'manifest_sha256':digest((HERE/(PREFIX+'-manifest.json')).read_bytes())},indent=2))
if __name__=='__main__':main()
