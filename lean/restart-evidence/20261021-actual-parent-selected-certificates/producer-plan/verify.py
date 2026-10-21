#!/usr/bin/env python3
"""Check the selected-certificate plan and its source snapshots."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',required=True,type=Path)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    manifest=json.loads((here/'manifest.json').read_text())
    for item in manifest['files']:
        path=Path(item['path'])
        assert not path.is_absolute() and '..' not in path.parts
        data=(here/path).read_bytes()
        assert len(data)==item['bytes'] and sha(data)==item['sha256'],str(path)
    pins=json.loads((here/'source-pins.json').read_text())
    assert pins['sources']==manifest['sources']
    ranges=[]
    for item in pins['sources']:
        path,snapshot=Path(item['path']),Path(item['snapshot'])
        assert not path.is_absolute() and '..' not in path.parts
        assert not snapshot.is_absolute() and '..' not in snapshot.parts
        data=(here/snapshot).read_bytes()
        assert len(data)==item['bytes'] and sha(data)==item['sha256'],str(path)
        lines=data.splitlines(keepends=True)
        for span in item['reviewed_ranges']:
            start,end=span['start'],span['end']
            assert 1<=start<=end<=len(lines)
            assert sha(b''.join(lines[start-1:end]))==span['sha256']
            ranges.append({'path':item['path'],**span})
        if args.live:
            assert sha((args.root/path).read_bytes())==item['sha256'],str(path)
    assert ranges==json.loads((here/'ranges.json').read_text())['ranges']
    selection=json.loads((here/'selection.json').read_text())
    assert selection['finalized'] and not selection['proposed_result_proved']
    assert not selection['signature_elaborated'] and not selection['official_edits']
    assert not selection['implementation_authorized_in_this_package']
    assert selection['proposed_public_heads']==['SourceCurrentActualParentSelectedCertificates.selected_certificates']
    for field in ('new_lean_commands','new_lake_commands','new_canonical_commands','new_public_pairs','new_constructed_pairs'):
        assert pins[field]==selection[field]==0
    plan=(here/'plan.md').read_text()
    for clause in ('SOURCE-ONLY PLAN','derive entry Current','COMPLETE selected records','No injectivity of `Record.paths`','ENTRY-indexed','A separate `ConjunctionClassScanSoundness.verified` invocation would be redundant','initial Merge StoredPlain','future ENCLOSING'):
        assert clause.lower() in plan.lower(),clause
    signature=(here/'proposed-signature.lean.txt').read_text()
    assert signature.count('theorem selected_certificates')==1
    for clause in ('numeric.actual =','Retained trace records kept','ScanReads trace memos scanMemos','PassReads formulas solver pass preparedMemos final','EndpointMemoGateTrace.Valid preparedHeap preparedMemos','(requiredCall :','(passCall :','(supported :','(causal :'):
        assert clause in signature,clause
    assert '(current :' not in signature and '(ranges :' not in signature
    print(json.dumps({'status':'PASS','live':args.live,'root_sources':len(pins['sources']),'reviewed_ranges':len(ranges),'pins':len(manifest['files'])+len(manifest['sources']),'new_lean_commands':0,'new_lake_commands':0,'new_canonical_commands':0,'new_public_pairs':0,'new_constructed_pairs':0,'proposal_proved':False,'manifest_sha256':sha((here/'manifest.json').read_bytes())},indent=2))

if __name__=='__main__':
    main()
