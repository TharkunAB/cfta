#!/usr/bin/env python3
"""Verify the frozen positive quotient-count component and selected readback."""
from __future__ import annotations
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='positive-quotient-count'
def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()
def main() -> None:
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--live',action='store_true');args=ap.parse_args()
    manifest=json.loads((HERE/(PREFIX+'-manifest.json')).read_text());assert manifest['finalized']
    for item in manifest['files']:
        data=(HERE/item['path']).read_bytes();assert len(data)==item['bytes'],item['path'];assert sha(data)==item['sha256'],item['path']
    selected=json.loads((HERE/(PREFIX+'-selection.json')).read_text());assert selected['finalized']
    source=(HERE/selected['source']).read_bytes();assert sha(source)==selected['source_sha256'];assert len(source.splitlines())==195
    if args.live:assert sha((args.root/selected['official_path']).read_bytes())==selected['source_sha256']
    checked=json.loads(subprocess.check_output([sys.executable,str(HERE/'check-full-public.py')],cwd='/'))
    assert checked==json.loads((HERE/'full-public-readback.json').read_text())
    assert checked['source_sha256']==sha(source)
    assert len(checked['heads'])==2 and checked['all_eight_printer_settings'] and checked['no_omissions']
    for h in checked['heads']:
        assert h['check_print_type_identity'] and h['unique_actual_lambda_body_delimiter']
        assert not h['private_public_type_names']
        assert set(h['actual_axioms'])<={'propext','Classical.choice','Quot.sound'}
        assert h['actual_axioms']==selected['actual_axioms_by_head'][h['head']]
    ledger=json.loads((HERE/'attempt-ledger.json').read_text());assert len(ledger['attempts'])==3
    exits=[]
    for attempt in ledger['attempts']:
        receipt=json.loads((HERE/attempt['receipt']).read_text());usage=json.loads((HERE/attempt['usage']).read_text());limits=json.loads((HERE/attempt['limits']).read_text())
        assert receipt['exit_code']==attempt['exit_code'];exits.append(receipt['exit_code'])
        assert sha((HERE/receipt['source']).read_bytes())==receipt['sha256']
        assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        assert usage['age_seconds']<=600 and usage['remaining_percent']>1
        assert receipt['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
        assert '-Dlinter.all=true' in receipt['command']
        assert not re.search(r'\bwarning(?:\([^)]*\))?:',(HERE/attempt['raw_log']).read_text())
    assert exits==[1,0,0]
    assert (HERE/(selected['selected_strict']+'.log')).stat().st_size==0
    proposed=(HERE/'inputs/plan/proposed-geometry-signatures.lean.txt').read_text()
    original_header=proposed[proposed.index('theorem child_count\n'):proposed.index('\n\nend MicroCFTA')]
    text=source.decode();actual_header=text[text.index('theorem child_count\n'):text.index(' := by\n',text.index('theorem child_count\n'))]
    assert original_header==actual_header
    assert 'noncomputable def count (inherited : List Record) (value : Node) : Nat := by' in text
    old=(HERE/'inputs/plan/sourcepins/SourceCurrentPositiveOwnerPair.lean').read_text().splitlines(keepends=True)
    assert ''.join(old[22:74]) in text
    bad=(HERE/(PREFIX+'-direct-1.source.lean')).read_text()
    assert bad.replace('counted.trans List.length_erase_le','Nat.le_trans counted List.length_erase_le')==text
    plan_command=[sys.executable,str(HERE/'inputs/plan/verify.py'),'--root',str(args.root)]
    if args.live:plan_command.append('--live')
    plan=json.loads(subprocess.check_output(plan_command,cwd='/'));assert plan['status']=='PASS'
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':plan['root_pins'],'actual_lean_jobs':3,'failed_jobs':1,'warning_jobs':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'full_public_heads':2,'actual_axioms_by_head':selected['actual_axioms_by_head'],'exact_public_type_identity':True,'all_eight_settings':True,'explicit_backwards_premise':True,'no_runtime_rank_claim':True,'copied_enumeration_lines':52,'manifest_sha256':sha((HERE/(PREFIX+'-manifest.json')).read_bytes())},indent=2))
if __name__=='__main__':main()
