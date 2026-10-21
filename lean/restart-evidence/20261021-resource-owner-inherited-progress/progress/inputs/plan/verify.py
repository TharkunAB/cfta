#!/usr/bin/env python3
"""Verify the any-inherited owner consumer plan and its stable inputs."""
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
    manifest=json.loads((HERE/'manifest.json').read_text())
    assert manifest['finalized'] and manifest['source_only'] and manifest['jobs']==0
    for pin in manifest['files']:check(HERE/relative(pin['path']),pin)
    pins=json.loads((HERE/'source-pins.json').read_text())['sources'];assert pins==manifest['sources']
    for pin in pins:
        snapshot=HERE/relative(pin['snapshot']);check(snapshot,pin);lines=snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['used_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert sha(b''.join(lines[lo-1:hi]))==span['sha256']
        if args.live:check(args.root/relative(pin['path']),pin)
    assert sha((HERE/'plan.md').read_bytes())=='25358f0d4589f3a4f741864c63f095d100fd3331e10d3fbadf6e793eeea03028'
    proposal=(HERE/'proposed-signature.lean.txt').read_text()
    assert sha(proposal.encode())=='9ef7489ee726e0b0eeac4f93bf36a0ade18202ead6c6783c3baf03b36ea368f9'
    assert re.findall(r'^theorem (\w+)',proposal,re.M)==['key_ne_inherited'] and ' := by' not in proposal
    assert '(identity : Nat)' not in proposal and '(top :' not in proposal
    assert 'child.1.payload ≠ request.inherited.payload' in proposal
    geometry=HERE/'inputs/geometry-compiler-checked';status=json.loads((HERE/'geometry-status.json').read_text())
    assert status['compiler_checked'] and not status['official_install_or_audit_claim'] and status['plan_jobs']==0
    source=(geometry/'SourceCurrentPositiveInheritedChildSeparation.lean').read_bytes();assert sha(source)==status['source_sha256']
    assert len(source.splitlines())==236
    for stem in ['positive-inherited-child-separation-direct-1','positive-inherited-child-separation-public-1']:
        receipt=json.loads((geometry/(stem+'.json')).read_text());assert receipt['exit_code']==0
        assert receipt['sha256']==sha((geometry/(stem+'.source.lean')).read_bytes())
    assert not (geometry/'positive-inherited-child-separation-direct-1.log').read_bytes()
    readback=json.loads((geometry/'full-public-readback.json').read_text())
    data=(geometry/'positive-inherited-child-separation-public-1.log').read_bytes()
    assert sha(data)==readback['log_sha256'] and len(data)==readback['log_bytes']==257297
    assert all(x['check_print_type_identity'] and set(x['actual_axioms'])=={'propext','Classical.choice','Quot.sound'}for x in readback['heads'])
    print(json.dumps({'status':'PASS','live':args.live,'finalized':True,'local_pins':len(manifest['files']),
        'root_pins':len(pins),'source_ranges':sum(len(x['used_ranges'])for x in pins),'jobs':0,
        'proposal_unproved':True,'geometry_compiler_receipts_pinned':True,
        'geometry_official_audit_claim':False,'authorship_disclosed':True,
        'manifest_sha256':sha((HERE/'manifest.json').read_bytes())},indent=2))
if __name__=='__main__':main()
