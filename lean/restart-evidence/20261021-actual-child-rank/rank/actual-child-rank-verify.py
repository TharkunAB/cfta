#!/usr/bin/env python3
"""Verify the one-hop rank proof, complete checks, and portable source pins."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = 'actual-child-rank'
def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/(PREFIX+'-manifest.json')).read_text())
    assert manifest['finalized']
    for pin in manifest['files']:
        data=(HERE/pin['path']).read_bytes()
        assert len(data)==pin['bytes'] and sha(data)==pin['sha256'],pin['path']
    selection=json.loads((HERE/(PREFIX+'-selection.json')).read_text())
    assert selection['finalized']
    source=(HERE/selection['source']).read_bytes()
    assert sha(source)==selection['source_sha256']
    assert len(source.splitlines())==selection['source_lines']<250
    if args.live:
        assert sha((args.root/selection['official_path']).read_bytes())==sha(source)
    checked=json.loads(subprocess.check_output([sys.executable,str(HERE/'check-full-public.py')],cwd='/'))
    assert checked==json.loads((HERE/'full-public-readback.json').read_text())
    assert checked['source_sha256']==sha(source)
    assert len(checked['heads'])==1 and checked['all_eight_printer_settings'] and checked['no_omissions']
    for head in checked['heads']:
        assert head['check_print_type_identity'] and head['unique_actual_lambda_body_delimiter']
        assert not head['private_public_type_names']
        assert set(head['actual_axioms'])<={'propext','Classical.choice','Quot.sound'}
        assert head['actual_axioms']==selection['actual_axioms_by_head'][head['head']]
    ledger=json.loads((HERE/'attempt-ledger.json').read_text())
    assert len(ledger['attempts'])==6
    exits=[]
    for attempt in ledger['attempts']:
        receipt=json.loads((HERE/attempt['receipt']).read_text())
        usage=json.loads((HERE/attempt['usage']).read_text())
        limits=json.loads((HERE/attempt['limits']).read_text())
        exits.append(receipt['exit_code'])
        assert receipt['exit_code']==attempt['exit_code']
        assert sha((HERE/receipt['source']).read_bytes())==receipt['sha256']
        assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        assert usage['age_seconds']<=600 and usage['remaining_percent']>1
        assert receipt['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
        assert '-Dlinter.all=true' in receipt['command']
        warned=bool(re.search(r'\bwarning(?:\([^)]*\))?:',(HERE/attempt['raw_log']).read_text()))
        assert warned==attempt['warning_bearing']
        assert warned==(attempt['name']==PREFIX+'-direct-4')
    assert exits==[1,1,1,1,0,0]
    strict=json.loads((HERE/(selection['selected_strict']+'.json')).read_text())
    assert strict['sha256']==sha(source)
    assert (HERE/(selection['selected_strict']+'.log')).stat().st_size==0
    proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
    proposed=proposal[proposal.index('theorem dispatch'):proposal.index('\nend MicroCFTA')]
    text=source.decode()
    actual=text[text.index('theorem dispatch'):text.index('\n := by\n',text.index('theorem dispatch'))]
    assert proposed==actual
    assert text.count('SourceCurrentResourceParentPositiveBack.children')==1
    assert text.count('SourceCurrentPositiveQuotientCount.child_count')==1
    assert '(active :' not in actual and 'handle' not in actual
    old=(HERE/(PREFIX+'-direct-1.source.lean')).read_text()
    second=(HERE/(PREFIX+'-direct-2.source.lean')).read_text()
    assert old.replace('Bool.and_eq_true.mp plain','Bool.and_eq_true_iff.mp plain')==second
    third=(HERE/(PREFIX+'-direct-3.source.lean')).read_text()
    fourth=(HERE/(PREFIX+'-direct-4.source.lean')).read_text()
    assert second.replace(
        'have smaller := shape_mass member (shape ownEmpty) (List.mem_of_getElem? selected)',
        'have smaller := shape_mass (entry := ownerEntry) (depth := ownerDepth) (free := ownerFree)\n'
        '                member (shape ownEmpty) (List.mem_of_getElem? selected)')==third
    assert third.replace('rw [payload]',
        'simp only [payload, SourceEqualityConstraintAllocation.Value.payload, Option.getD_some]')==fourth
    assert fourth.replace(
        'simp only [payload, SourceEqualityConstraintAllocation.Value.payload, Option.getD_some]',
        'rw [payload]; simp only [SourceEqualityConstraintAllocation.Value.payload, Option.getD_some]')==text
    plan_command=[sys.executable,str(HERE/'inputs/plan/verify.py'),'--root',str(args.root)]
    if args.live:
        plan_command.append('--live')
    plan=json.loads(subprocess.check_output(plan_command,cwd='/'))
    assert plan['status']=='PASS'
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),
        'root_pins':plan['root_pins']+1,'actual_lean_jobs':6,'failed_jobs':4,
        'warning_jobs':1,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,
        'full_public_heads':1,'actual_axioms_by_head':selection['actual_axioms_by_head'],
        'exact_public_type_identity':True,'all_eight_settings':True,
        'no_active_owner_or_caller_back_premise':True,
        'actual_one_hop_rank_only':True,'older_lineage_and_completion_unproved':True,
        'mandatory_stop_preserved_and_authorized_trim':True,
        'authored_foundations_disclosed':True,
        'manifest_sha256':sha((HERE/(PREFIX+'-manifest.json')).read_bytes())},indent=2))

if __name__=='__main__':
    main()
