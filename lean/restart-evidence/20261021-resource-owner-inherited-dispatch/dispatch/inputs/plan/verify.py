#!/usr/bin/env python3
"""Verify the source-only inherited-owner dispatch plan."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def relative(value: str) -> Path:
    result=Path(value)
    assert not result.is_absolute() and '..' not in result.parts,value
    return result

def check(path: Path,pin: dict) -> None:
    assert path.is_file() and path.stat().st_size==pin['bytes'] and sha(path)==pin['sha256'],str(path)

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'manifest.json').read_text())
    assert manifest['finalized'] and manifest['source_only']
    assert manifest['lean_jobs']==manifest['canonical_jobs']==manifest['runtime_jobs']==manifest['public_pairs']==0
    assert manifest['official_edits'] is False
    for pin in manifest['files']:
        check(HERE/relative(pin['path']),pin)
    sources=json.loads((HERE/'source-pins.json').read_text())['sources']
    assert sources==manifest['sources'] and len(sources)==6
    for pin in sources:
        snapshot=HERE/relative(pin['snapshot'])
        check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines)==pin['lines']
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end']
            assert 1<=lo<=hi<=len(lines)
            assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()==span['sha256']
        if args.live:
            check(args.root/relative(pin['path']),pin)
    proposal=(HERE/'proposed-signature.lean.txt').read_text()
    assert len(proposal.splitlines())==68
    assert sha(HERE/'proposed-signature.lean.txt')=='4e7b2816584ae038134eb1c827b0d11de0f60befe395df825cc7bda99aaecf45'
    assert re.findall(r'^theorem (\w+)',proposal,re.M)==['key_ne_inherited']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|:= by|_private',proposal)
    old=(HERE/'inputs/top-proposed-signature.lean.txt').read_text()
    expected=old.replace('SourceCurrentResourceOwnerDispatch','SourceCurrentResourceOwnerInheritedDispatch').replace('key_ne_top','key_ne_inherited').replace('{g s r e p h m c n budget fuel slot handle identity : Nat}','{g s r e p h m c n budget fuel slot handle : Nat}\n    {inherited : EqValue}').replace('(.live identity [])','inherited').replace('.live identity [],','inherited,')
    assert proposal==expected and 'identity' not in proposal and '.live' not in proposal
    top=(HERE/'inputs/root/lean/MicroCFTA/SourceCurrentResourceOwnerDispatch.lean').read_text()
    assert top.split('theorem key_ne_top\n',1)[1].split(' := by',1)[0]==old.split('theorem key_ne_top\n',1)[1].split('\nend MicroCFTA.',1)[0]
    top_selection=json.loads((HERE/'inputs/top-selection.json').read_text())
    assert top_selection['source_sha256']==sha(HERE/'inputs/root/lean/MicroCFTA/SourceCurrentResourceOwnerDispatch.lean')
    assert top_selection['selected_strict']=='resource-owner-dispatch-direct-2' and top_selection['selected_public']=='resource-owner-dispatch-public-1'
    consumer=HERE/'inputs/consumer-proposed-signature.lean.txt'
    assert sha(consumer)=='9ef7489ee726e0b0eeac4f93bf36a0ade18202ead6c6783c3baf03b36ea368f9'
    status=json.loads((HERE/'dependency-status.json').read_text())
    assert status['checked'] is False and status['proposal_sha256']==sha(consumer)
    scope=json.loads((HERE/'scope.json').read_text())
    for key in ['lean_jobs','lake_jobs','canonical_jobs','runtime_jobs','new_public_pairs','constructed_pairs']:
        assert scope[key]==0
    assert scope['official_edits'] is False and scope['pending_consumer_checked'] is False
    original=HERE/'reviewed-plan-original.md'
    assert sha(original)=='bffd72181c2c51df54b69b583a388a177f2db0432fd11e5d0339f8273c49748b'
    assert (HERE/'plan.md').read_text()==original.read_text()+'\n'+(HERE/'consumer-status-addendum.md').read_text()
    current=json.loads((HERE/'current-consumer-status.json').read_text())
    assert current['checked'] is False and current['candidate_reported_lines']==241
    assert current['candidate_reported_sha256_prefix']=='aae1b162' and current['second_strict_status']=='running at root cue'
    assert current['public_api_sha256']==sha(consumer) and current['consumer_jobs_owned_by_this_plan']==0
    assert not list(HERE.glob('*.lean')) and not list(HERE.glob('*.olean')) and not list(HERE.glob('*.log'))
    print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),root_pins=len(sources),source_ranges=sum(len(p['reviewed_ranges']) for p in sources),lean_jobs=0,canonical_jobs=0,runtime_jobs=0,public_pairs=0,proposed_public_head='MicroCFTA.SourceCurrentResourceOwnerInheritedDispatch.key_ne_inherited',consumer_checked_at_plan_cue=False,manifest_sha256=sha(HERE/'manifest.json')),indent=2))

if __name__=='__main__':
    main()
