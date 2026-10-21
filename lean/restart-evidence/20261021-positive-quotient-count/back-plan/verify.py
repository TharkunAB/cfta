#!/usr/bin/env python3
"""Verify the source-only all-child positive ancestry plan."""
from __future__ import annotations
import argparse
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
    assert pins==manifest['sources'] and len(pins)==10
    for pin in pins:
        snapshot=HERE/rel(pin['snapshot']);check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines)==pin['lines']
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()==span['sha256']
        if args.live:
            check(args.root/rel(pin['path']),pin)
    assert sha(HERE/'plan.md')=='ab39794d6c4a2bc1a72a0704d631316114b967421c6dc1508ab32ba966cbabc5'
    assert sha(HERE/'proposed-signature.lean.txt')=='ba9ca033d86744dfeed8084e25cbd764f1383e5bfa79a642107e68c5d40df513'
    proposal=(HERE/'proposed-signature.lean.txt').read_text()
    assert len(proposal.splitlines())==38
    assert re.findall(r'^theorem (\w+)',proposal,re.M)==['children']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|:= by|_private',proposal)
    assert proposal.count('SourceCurrentResourceParentWriters.Written')==1
    assert 'sourceEqualities request.value.entry.key.constraint = some []' in proposal
    assert 'Shape request.value returned' in proposal
    assert '∀ outputIndex child, returned.children[outputIndex]? = some child' in proposal
    assert '∀ residual, PositiveAt child residual' in proposal
    assert 'request.value.children[inputIndex]? = some original' in proposal
    assert 'Rel (classes.map SourceEqualityClassOrder.Record.paths)' in proposal
    assert 'laterGrowth' not in proposal and 'ownerRows' not in proposal and 'foundOwner' not in proposal
    erratum=json.loads((HERE/'source-citation-erratum.json').read_text())
    assert erratum['approved_plan_sha256']==sha(HERE/'plan.md')
    assert erratum['plan_bytes_unchanged'] and erratum['public_type_unchanged'] and erratum['mathematical_contract_unchanged']
    assert len(erratum['corrections'])==5
    scope=json.loads((HERE/'scope.json').read_text())
    for key in ['lean_jobs','lake_jobs','canonical_jobs','runtime_jobs','public_pairs','constructed_pairs']:
        assert scope[key]==0
    assert scope['public_type_elaborated'] is False and scope['official_edits'] is False
    assert not list(HERE.glob('*.lean')) and not list(HERE.glob('*.olean')) and not list(HERE.glob('*.log'))
    print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),root_pins=len(pins),source_ranges=sum(len(x['reviewed_ranges']) for x in pins),lean_jobs=0,canonical_jobs=0,runtime_jobs=0,public_pairs=0,proposed_public_head=scope['proposed_public_head'],public_type_elaborated=False,manifest_sha256=sha(HERE/'manifest.json')),indent=2))

if __name__=='__main__':
    main()
