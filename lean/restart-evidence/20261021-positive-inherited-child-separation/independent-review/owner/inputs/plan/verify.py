#!/usr/bin/env python3
"""Verify the scoped source-only plan and its exact source ranges."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path
HERE=Path(__file__).resolve().parent

def sha(data:bytes)->str:
    return hashlib.sha256(data).hexdigest()

def relative(value:str)->Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path

def check(path:Path,pin:dict)->None:
    data=path.read_bytes()
    assert len(data)==pin['bytes'] and sha(data)==pin['sha256'],str(path)

def main()->None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'manifest.json').read_text())
    scope=json.loads((HERE/'scope.json').read_text())
    assert manifest['finalized'] and scope['finalized']
    assert scope['new_lean_lake_canonical_runtime_jobs']==0
    assert not scope['official_edits'] and not scope['proof_source_drafted']
    assert not scope['new_theorem'] and not scope['counterexample']
    assert not scope['manual_regeneration_computation_checked']
    for pin in manifest['files']:check(HERE/relative(pin['path']),pin)
    sources=json.loads((HERE/'source-pins.json').read_text())['sources']
    assert sources==manifest['sources']
    for pin in sources:
        path=HERE/relative(pin['snapshot']);check(path,pin)
        lines=path.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert sha(b''.join(lines[lo-1:hi]))==span['sha256']
        if args.live:check(args.root/relative(pin['path']),pin)
    contract=(HERE/'proposed-signature.lean.txt').read_text()
    assert re.findall(r'^theorem (\w+)',contract,re.M)==scope['proposed_public_heads']
    assert ' := by' not in contract
    assert sha((HERE/'plan.md').read_bytes())=='5620d41fe6fb3118971d2431a6b9e8a239ec178d8954a7e0e1796491530bedfb'
    assert sha(contract.encode())=='865bfc47994e091250bd57680a6410140c1654f28fefea29642dcdf0ad3ad07a'
    original=(HERE/'inputs/root/lean/MicroCFTA/SourceCurrentPositiveOwnerPair.lean').read_bytes().splitlines(keepends=True)
    assert (HERE/'finite-enumeration-input.lean.txt').read_bytes()==b''.join(original[22:78])
    assert sha((HERE/'inputs/frontier/manifest.json').read_bytes())=='8a60b8deee80bef1864686cd30f7023d6c9a5f799f08d6e94d71a495ffe252c0'
    print(json.dumps({'status':'PASS','live':args.live,'finalized':True,'local_pins':len(manifest['files']),
        'root_pins':len(sources),'reviewed_ranges':sum(len(x['reviewed_ranges'])for x in sources),
        'jobs':0,'new_theorem':False,'counterexample':False,'authorship_disclosed':True,
        'public_contracts_unproved':scope['proposed_public_heads'],
        'manifest_sha256':sha((HERE/'manifest.json').read_bytes())},indent=2))
if __name__=='__main__':main()
