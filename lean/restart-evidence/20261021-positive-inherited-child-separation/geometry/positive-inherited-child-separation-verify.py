#!/usr/bin/env python3
"""Verify the geometry proof evidence without a Lean command."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='positive-inherited-child-separation-'

def sha(data:bytes)->str:
    return hashlib.sha256(data).hexdigest()

def relative(value:str)->Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts,value
    return path

def check(path:Path,pin:dict)->None:
    data=path.read_bytes()
    assert len(data)==pin['bytes'] and sha(data)==pin['sha256'],str(path)

def main()->None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',required=True,type=Path)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/(PREFIX+'manifest.json')).read_text())
    selection=json.loads((HERE/(PREFIX+'selection.json')).read_text())
    assert manifest['finalized'] and selection['finalized']
    for pin in manifest['files']:check(HERE/relative(pin['path']),pin)
    pins=json.loads((HERE/(PREFIX+'source-pins.json')).read_text())['sources']
    assert pins==manifest['sources']
    for pin in pins:
        snapshot=HERE/relative(pin['snapshot']);check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert sha(b''.join(lines[lo-1:hi]))==span['sha256']
        if args.live:check(args.root/relative(pin['path']),pin)
    source=(HERE/selection['source']).read_text()
    assert sha(source.encode())==selection['source_sha256']
    assert len(source.splitlines())==selection['source_lines']==236
    if args.live:
        assert sha((args.root/selection['official_path']).read_bytes())==selection['source_sha256']
    assert re.findall(r'^theorem (\w+)',source,re.M)==['child_reflect','same_child_payload_ne']
    assert not re.search(r'\b(?:sorry|axiom|admit|native_decide|trustCompiler)\b|_private',source)
    proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
    heads=['child_reflect','same_child_payload_ne']
    for i,name in enumerate(heads):
        actual=source.split('theorem '+name,1)[1].split(' := by',1)[0].strip()
        expected=proposal.split('theorem '+name,1)[1].split('\ntheorem '+heads[i+1],1)[0] if i+1<len(heads) else proposal.split('theorem '+name,1)[1].split('\nend MicroCFTA.',1)[0]
        assert actual==expected.strip(),name
    assert source.count((HERE/'finite-enumeration-used.lean.txt').read_text())==1
    assert 'positivePaths_nodup' not in source
    enum_source=(HERE/'inputs/plan/inputs/root/lean/MicroCFTA/SourceCurrentPositiveOwnerPair.lean').read_bytes().splitlines(keepends=True)
    assert (HERE/'finite-enumeration-used.lean.txt').read_bytes()==b''.join(enum_source[22:74])
    for stem in (selection['selected_strict'],selection['selected_public']):
        receipt=json.loads((HERE/(stem+'.json')).read_text())
        assert receipt['exit_code']==0
        assert receipt['sha256']==sha((HERE/(stem+'.source.lean')).read_bytes())
        assert receipt['command'][1]=='-Dlinter.all=true'
        assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
        assert json.loads((HERE/(stem+'.limits.json')).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=json.loads((HERE/(stem+'.usage.json')).read_text())
        assert usage['remaining_percent']>1 and 0<=usage['age_seconds']<=600
    assert not (HERE/(selection['selected_strict']+'.log')).read_bytes()
    assert (HERE/(selection['selected_strict']+'.source.lean')).read_text()==source
    ledger=json.loads((HERE/(PREFIX+'attempt-ledger.json')).read_text())
    assert ledger['actual_lean_jobs']==2 and ledger['failed']==ledger['warned']==ledger['canonical']==0
    checked=subprocess.run([sys.executable,str(HERE/'check-full-public.py')],cwd='/',env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True)
    assert checked.returncode==0,(checked.stdout,checked.stderr)
    readback=json.loads(checked.stdout)
    assert readback==json.loads((HERE/'full-public-readback.json').read_text())
    assert readback['log_bytes']==selection['public_log_bytes'] and readback['log_sha256']==selection['public_log_sha256']
    print(json.dumps({'status':'PASS','live':args.live,'finalized':True,'local_pins':len(manifest['files']),
        'root_pins':len(pins),'actual_lean_jobs':2,'failures':0,'warnings':0,'canonical_jobs':0,
        'constructed_pairs':0,'public_pairs':2,'full_proofs':True,'all_eight_settings':True,
        'exact_public_type_identity':True,'standard_axioms_per_head':True,'geometry_scope_only':True,
        'copied_enumeration_disclosed':True,'manifest_sha256':sha((HERE/(PREFIX+'manifest.json')).read_bytes())},indent=2))
if __name__=='__main__':main()
