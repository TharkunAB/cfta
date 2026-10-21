#!/usr/bin/env python3
"""Verify the source-only body-rank composition plan without running Lean."""
from __future__ import annotations
import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(value: str) -> Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts,value
    return path


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
        check(HERE/rel(pin['path']),pin)
    pins=json.loads((HERE/'source-pins.json').read_text())['sources']
    assert pins==manifest['sources'] and len(pins)==12
    for pin in pins:
        snapshot=HERE/rel(pin['snapshot']);check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines)==pin['lines']
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()==span['sha256']
        if args.live:
            check(args.root/rel(pin['path']),pin)
    assert sha(HERE/'plan.md')=='d61d01f109fbf99d9443bc075f7905d12b0cf278834c2c6094ffac8b998db0d3'
    assert sha(HERE/'proposed-signature.lean.txt')=='029a76efa31ebf7d39d357555267b91b95e626cc409a09c35cfaa203f5b75ecb'
    original=(HERE/'plan-before-context-simplification.md').read_text()
    current=(HERE/'plan.md').read_text()
    assert sha(HERE/'plan-before-context-simplification.md')=='c7d3e7d67688a733748e98816502cfad9a779f2be7acf2ac35eef73ee1cb74ea'
    patch=''.join(difflib.unified_diff(original.splitlines(keepends=True),current.splitlines(keepends=True),fromfile='plan-before-context-simplification.md',tofile='plan.md'))
    assert patch==(HERE/'context-simplification.patch').read_text()
    delta=json.loads((HERE/'context-simplification.json').read_text())
    assert delta['original_plan_sha256']==sha(HERE/'plan-before-context-simplification.md')
    assert delta['updated_plan_sha256']==sha(HERE/'plan.md')
    assert delta['public_type_unchanged'] and delta['mathematical_contract_unchanged'] and delta['lean_jobs']==0
    proposal=(HERE/'proposed-signature.lean.txt').read_text()
    assert len(proposal.splitlines())==39
    assert re.findall(r'^theorem (\w+)',proposal,re.M)==['body_rank_lt']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|:= by|_private',proposal)
    assert proposal.split('theorem body_rank_lt',1)[1].count('Prod.Lex Nat.lt Nat.lt')==1
    assert '(.body ownerFuel owner running)' in proposal and '(.node candidateFuel candidate current)' in proposal
    assert 'NodeIdle' not in proposal and 'original ∈' not in proposal
    assert 'candidate.inherited.payload.getD []' in proposal and 'owner.inherited.payload.getD []' in proposal
    status=json.loads((HERE/'dependency-status.json').read_text())
    assert status['body_rank']['unchanged_frozen_lineage_type']
    assert status['body_rank']['proposal_sha256']==sha(HERE/'proposed-signature.lean.txt')
    assert status['body_rank']['status']=='unproved source-only proposal'
    draft=HERE/'inputs/one-hop-unproved-draft.lean.txt'
    assert sha(draft)==status['one_hop']['source_sha256']=='e029a3ab616437a4a05ebd4ef170834c94b945f8b39d3dc1b0bfde6c8a9c19ce'
    assert len(draft.read_text().splitlines())==status['one_hop']['source_lines']==250
    assert status['one_hop']['source_review_limit_reached']
    assert 'unproved' in status['one_hop']['status'] and 'zero compiler jobs' in status['one_hop']['status']
    onehop=HERE/'inputs/one-hop-proposed-signature.lean.txt'
    assert sha(onehop)==status['one_hop']['proposal_sha256']=='decddee6eb4eaa0a9168616c12045f7f18e504d16b748413a60a1c75bb960cd8'
    assert draft.read_text().split('theorem dispatch\n',1)[1].split('\n := by',1)[0].removesuffix('\n')==onehop.read_text().split('theorem dispatch\n',1)[1].split('\n\nend MicroCFTA.',1)[0]
    for key in ['lean_jobs','canonical_jobs','runtime_jobs']:
        assert status[key]==0
    assert status['official_edits'] is False
    later=json.loads((HERE/'one-hop-later-status.json').read_text())
    assert later['source_sha256']==sha(HERE/'inputs/one-hop-later-unproved-draft.lean.txt')=='fd5eade86cfb9843c19fdad1653c66eec02fd692712f944a47850ecf5d4122be'
    assert later['source_lines']==len((HERE/'inputs/one-hop-later-unproved-draft.lean.txt').read_text().splitlines())==248
    assert later['proof_jobs_owned_here']==0 and later['public_api_unchanged']
    assert 'Unproved' in later['status'] and later['actual_failed_strict_jobs_at_cue']==1
    scope=json.loads((HERE/'scope.json').read_text())
    for key in ['lean_jobs','lake_jobs','canonical_jobs','runtime_jobs','public_pairs','constructed_pairs']:
        assert scope[key]==0
    assert scope['public_type_elaborated'] is False and scope['official_edits'] is False
    assert not list(HERE.glob('*.lean')) and not list(HERE.glob('*.olean')) and not list(HERE.glob('*.log'))
    print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),root_pins=len(pins),source_ranges=sum(len(x['reviewed_ranges']) for x in pins),lean_jobs=0,canonical_jobs=0,runtime_jobs=0,public_pairs=0,proposed_public_head=scope['proposed_public_head'],public_type_elaborated=False,pending_one_hop_is_not_proved=True,manifest_sha256=sha(HERE/'manifest.json')),indent=2))


if __name__=='__main__':
    main()
