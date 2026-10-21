#!/usr/bin/env python3
"""Verify the independent source-only Parent store plan review."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

def sha(data:bytes)->str:return hashlib.sha256(data).hexdigest()
def main()->None:
    parser=argparse.ArgumentParser();parser.add_argument('--root',required=True,type=Path);parser.add_argument('--live',action='store_true');args=parser.parse_args()
    here=Path(__file__).resolve().parent
    manifest=json.loads((here/'manifest.json').read_text())
    for pin in manifest['files']:
        path=Path(pin['path']);assert not path.is_absolute() and '..' not in path.parts
        data=(here/path).read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256'],str(path)
    pins=json.loads((here/'source-pins.json').read_text())['sources'];assert pins==manifest['sources']
    ranges=[]
    for pin in pins:
        path,snapshot=Path(pin['path']),Path(pin['snapshot'])
        assert not path.is_absolute() and '..' not in path.parts and not snapshot.is_absolute() and '..' not in snapshot.parts
        data=(here/snapshot).read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256'],str(path)
        lines=data.splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert sha(b''.join(lines[lo-1:hi]))==span['sha256']
            ranges.append({'path':pin['path'],**span})
        if args.live:assert sha((args.root/path).read_bytes())==pin['sha256'],str(path)
    assert ranges==json.loads((here/'ranges.json').read_text())['ranges']
    selected=json.loads((here/'selection.json').read_text());assert selected['finalized'] and selected['review_clear']
    assert not selected['proposal_proved'] and not selected['signature_elaborated'] and not selected['official_edits']
    for field in ('new_lean_commands','new_lake_commands','new_canonical_commands','new_public_pairs','new_constructed_pairs'):
        assert selected[field]==0
    owner=here/'inputs/owner'
    assert sha((owner/'manifest.json').read_bytes())=='7214556dfa977c5b2d93cc05d48568ef6ae3a3cb318f70db9e43755c93e44647'
    owner_manifest=json.loads((owner/'manifest.json').read_text())
    for pin in owner_manifest['files']:
        data=(owner/pin['path']).read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256']
    plan=(owner/'plan.md').read_text();signature=(owner/'proposed-signature.lean.txt').read_text()
    assert len(plan.splitlines())==59 and len(signature.splitlines())==43
    assert signature.count('theorem parent')==1
    for clause in ('(initial : Context','(frame : Frame','(reserved :','(normal :','(supported :','(causal :','(merged :','(positiveMemo :','(observed :','∃ next final, SourceCurrentParentNumeric.Receipt','Support after.native.machine.heap after.native','Support saved'):
        assert clause in signature,clause
    assert '(current :' not in signature and '(ranges :' not in signature
    for clause in ('Keep these internal children separate from `result.children`','A stopped Scan can contain earlier real queries','PHYSICAL HEAP `nodeRecords`','It does not recover native laws at an earlier historical Parent writer'):
        assert clause in plan,clause
    report=(here/'review.md').read_text()
    assert 'source-only clearance' in report and 'No material mathematical or scope blocker' in report
    assert 'The reviewer did not author that module' in report or 'the reviewer did not author that module' in report
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),'reviewed_ranges':len(ranges),'new_lean_commands':0,'new_lake_commands':0,'new_canonical_commands':0,'new_public_pairs':0,'new_constructed_pairs':0,'proposal_proved':False,'signature_elaborated':False,'source_review_clear':True,'manifest_sha256':sha((here/'manifest.json').read_bytes())},indent=2))
if __name__=='__main__':main()
