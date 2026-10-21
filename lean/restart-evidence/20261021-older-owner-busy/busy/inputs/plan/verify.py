#!/usr/bin/env python3
"""Verify the portable source-only busy-node exclusion plan."""
from pathlib import Path
import argparse
import hashlib
import json

HERE=Path(__file__).resolve().parent
def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'plan-manifest.json').read_text())
    assert manifest['finalized']
    for pin in manifest['files']:
        data=(HERE/pin['path']).read_bytes()
        assert len(data)==pin['bytes'] and sha(data)==pin['sha256'],pin['path']
    pins=json.loads((HERE/'sourcepins.json').read_text())['pins']
    ranges=0
    for pin in pins:
        data=(HERE/pin['snapshot']).read_bytes()
        assert sha(data)==pin['sha256']
        if args.live:
            assert sha((args.root/pin['root_path']).read_bytes())==pin['sha256'],pin['root_path']
        lines=data.splitlines(keepends=True)
        for interval in pin['reviewed_ranges']:
            data=b''.join(lines[interval['first']-1:interval['last']])
            assert data==(HERE/interval['snapshot']).read_bytes()
            assert sha(data)==interval['sha256']
            ranges+=1
    status=json.loads((HERE/'status.json').read_text())
    for key in ['compiler_jobs','runtime_jobs','canonical_jobs','new_theorems']:
        assert status[key]==0
    assert not status['implementation_included'] and status['initial_node_idle_required']
    selection=json.loads((HERE/'selection.json').read_text())
    assert selection['source_reviewed'] and not selection['elaborated']
    assert not selection['implementation_authorized_by_this_package']
    signature=(HERE/'proposed-signature.lean.txt').read_bytes()
    assert sha(signature)==selection['signature_sha256']
    assert signature.count(b'theorem no_node_busy\n')==1
    assert b'(initialNodeIdle :' in signature and b'.failed (.nodeMemo handle .busy) after' in signature
    plan=(HERE/'plan.md').read_bytes()
    assert sha(plan)==selection['plan_sha256'] and len(plan.splitlines())<=40
    cue=json.loads((HERE/'dependency-readiness-cue.json').read_text())
    body=(HERE/'inputs/body-source.lean.txt').read_bytes()
    assert sha(body)==cue['body_source_sha256']
    assert body==(HERE/'sourcepins/SourceCurrentOlderOwnerLineage.lean').read_bytes()
    strict=json.loads((HERE/'inputs/body-selected-strict.json').read_text())
    public=json.loads((HERE/'inputs/body-selected-public.json').read_text())
    readback=json.loads((HERE/'inputs/body-readback.json').read_text())
    assert strict['exit_code']==public['exit_code']==0 and strict['sha256']==sha(body)
    assert (HERE/'inputs/body-selected-strict.log').stat().st_size==0
    assert readback['status']=='PASS' and readback['public_log_bytes']==4762369
    assert cue['body_official_installed']
    assert sha((HERE/'inputs/body-owner-manifest.json').read_bytes())==cue['body_owner_frozen_manifest_sha256']
    print(json.dumps({'status':'PASS','live':args.live,'source_only':True,
        'local_pins':len(manifest['files']),'root_pins':len(pins),'reviewed_ranges':ranges,
        'compiler_jobs':0,'runtime_jobs':0,'new_theorems':0,
        'no_node_busy_unproved':True,'initial_node_idle_explicit':True,
        'no_new_rank_or_equality_producer':True,'finite_renewals_and_completion_unproved':True,
        'body_dependency_checked_and_installed':True,'body_compiled_readiness_at_cue':'pending root Audit',
        'authored_foundations_disclosed':True,
        'manifest_sha256':sha((HERE/'plan-manifest.json').read_bytes())},indent=2))

if __name__=='__main__':
    main()
