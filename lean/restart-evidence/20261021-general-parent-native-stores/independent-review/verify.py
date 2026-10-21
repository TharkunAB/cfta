#!/usr/bin/env python3
"""Verify the independent completed-Parent native-store proof review."""
from __future__ import annotations
import argparse, hashlib, json, os, re, subprocess, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE='SourceCurrentActualParentNativeStores.lean'
FINAL='f0a01cf4c787c523b29f357b0d6f0917576dce06db0c6daa684b4fee9ed7b75b'
HEAD='MicroCFTA.SourceCurrentActualParentNativeStores.parent'
def sha(data:bytes)->str:return hashlib.sha256(data).hexdigest()
def check(path:Path,pin:dict)->None:
    data=path.read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256'],str(path)
def normalized(text:str)->str:return re.sub(r'\s+',' ',text).strip()
def main()->None:
    parser=argparse.ArgumentParser();parser.add_argument('--root',required=True,type=Path);parser.add_argument('--live',action='store_true');args=parser.parse_args()
    manifest=json.loads((HERE/'manifest.json').read_text());assert manifest['finalized'] and manifest['independent_review']
    assert manifest['owned_lean_lake_commands']==manifest['owned_public_pairs']==0
    for pin in manifest['files']:
        path=Path(pin['path']);assert not path.is_absolute() and '..' not in path.parts;check(HERE/path,pin)
    pins=json.loads((HERE/'source-pins.json').read_text())['sources'];assert pins==manifest['sources']
    for pin in pins:
        check(HERE/pin['snapshot'],pin)
        lines=(HERE/pin['snapshot']).read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert sha(b''.join(lines[lo-1:hi]))==span['sha256']
        if args.live:check(args.root/pin['path'],pin)
    owner=HERE/'inputs/owner';source=(owner/SOURCE).read_text();assert sha(source.encode())==FINAL and len(source.splitlines())==262
    assert re.findall(r'^theorem (\w+)',source,re.M)==['parent']
    assert not re.search(r'\b(?:sorry|axiom|admit|native_decide|trustCompiler)\b|_private',source)
    proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text().split('theorem parent',1)[1]
    public=source.split('theorem parent',1)[1].split(' := by',1)[0]
    assert public.strip()==proposal.strip()
    for token in ('SourceCurrentActualParentSemanticReads.parent formulas solver inventory budget','SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan','SourceCurrentRequiredPositiveChronology.pass formulas solver requiredInventory requiredReceipt','SourceCurrentScanNumeric.complete formulas solver','SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard children'):
        assert source.count(token)==1,token
    assert source.count('SourceCurrentScanNativeStores.scan formulas solver scan')==2
    assert 'admitted.advance _ extension' not in source
    assert 'cases SourceEqualityMkEdgeAllocation.accepted (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard)' in source
    assert 'dsimp only at scanDone' in source and '.trans causal interval' in source
    assert sha((owner/'parent-native-stores-prelaunch.source.lean').read_bytes())=='39d513716fe26c16a37cbf100aeaba527251c3fea549ade0a246a93abef12a5e'
    assert sha((owner/'parent-native-stores-direct-1.source.lean').read_bytes())=='ca816e771a1cca671dfd2f3fa9340214cbe878a4637da6ba3835b878597f6ba4'
    assert not (owner/'parent-native-stores-direct-2.log').read_bytes()
    log_path=owner/'parent-native-stores-public-1.log';data=log_path.read_bytes();assert len(data)==8857109 and sha(data)=='169f2c16b7183f23c109ff6b511eac29332ab56760146cf197a5de2d6e1568d6'
    log=data.decode();assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    printer=(owner/'parent-native-stores-public-1.source.lean').read_text();assert printer.startswith(source)
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert printer.count('set_option '+option)==1
    checked,theorem=log.split('@'+HEAD+' :',1)[1].split('\ntheorem '+HEAD,1);typ,proof=theorem.split(' :=',1)
    assert normalized(checked)==normalized(typ.removeprefix(' :')) and '_private' not in checked+typ and len(proof)>1000
    match=re.search(re.escape("'"+HEAD+"' depends on axioms:")+r'\s*\[([^\]]*)\]',log);assert match
    assert {re.sub(r'\.\{[^}]*\}','',x.strip()) for x in match.group(1).split(',')}=={'propext','Classical.choice','Quot.sound'}
    command=[sys.executable,str(owner/'parent-native-stores-verify.py'),'--root',str(args.root)]
    if args.live:command.append('--live')
    result=subprocess.run(command,cwd='/',env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True)
    assert result.returncode==0,(result.stdout,result.stderr)
    owner_result=json.loads(result.stdout);assert owner_result['status']=='PASS'
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),'independent_review':True,'material_open_issues':0,'owned_lean_lake_commands':0,'owned_public_pairs':0,'reused_lean_jobs':3,'reused_failures':1,'reused_warning_bearing_failed_checks':1,'reused_canonical_jobs':0,'reused_public_pairs':1,'prelaunch_repair_lean_commands':0,'full_public_log_bytes':len(data),'public_type_identity':True,'all_eight_printer_settings':True,'standard_axioms_only':True,'authored_dependencies_disclosed':True,'manifest_sha256':sha((HERE/'manifest.json').read_bytes()),'frozen_owner_checker':owner_result},indent=2))
if __name__=='__main__':main()
