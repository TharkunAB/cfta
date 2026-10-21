#!/usr/bin/env python3
"""Verify the portable one-hop rank source plan and its source ranges."""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'plan-manifest.json').read_text())
    assert manifest['finalized']
    for pin in manifest['files']:
        data=(HERE/pin['path']).read_bytes()
        assert len(data)==pin['bytes'] and sha(data)==pin['sha256'], pin['path']
    sources=json.loads((HERE/'sourcepins.json').read_text())['pins']
    count=0
    for pin in sources:
        data=(HERE/pin['snapshot']).read_bytes()
        assert sha(data)==pin['sha256']
        if args.live:
            assert sha((args.root/pin['root_path']).read_bytes())==pin['sha256'],pin['root_path']
        lines=data.splitlines(keepends=True)
        for interval in pin['reviewed_ranges']:
            selected=b''.join(lines[interval['first']-1:interval['last']])
            assert selected==(HERE/interval['snapshot']).read_bytes()
            assert sha(selected)==interval['sha256']
            count+=1
    status=json.loads((HERE/'status.json').read_text())
    for key in ['compiler_jobs','runtime_jobs','canonical_jobs','new_theorems','counterexample_executions']:
        assert status[key]==0
    assert status['mandatory_source_stop']==250 and status['no_active_owner_premise']
    selection=json.loads((HERE/'selection.json').read_text())
    assert selection['source_reviewed'] and not selection['elaborated']
    assert not selection['implementation_authorized_by_this_package']
    signature=(HERE/'proposed-signature.lean.txt').read_text()
    assert sha(signature.encode())==selection['signature_sha256']
    assert signature.count('theorem dispatch\n')==1
    assert '(active :' not in signature and 'Prod.Lex Nat.lt Nat.lt' in signature
    plan=(HERE/'plan.md').read_text()
    old=(HERE/'plan-before-scope-stop.md').read_text()
    assert sha(plan.encode())==selection['plan_sha256']
    erratum=json.loads((HERE/'scope-stop-erratum.json').read_text())
    assert sha(old.encode())==erratum['original_plan_sha256']
    assert sha(plan.encode())==erratum['corrected_plan_sha256']
    assert 'STOP AT250lines BEFORE any compiler job or further machinery' in plan
    assert 'It is not a checked dependency yet.' in plan
    cue=json.loads((HERE/'checked-dependency-cue.json').read_text())
    assert cue['historical_plan_status_preserved'] and cue['back_official_installed']
    assert cue['this_package_compiler_jobs']==0
    print(json.dumps({'status':'PASS','live':args.live,'source_only':True,
        'local_pins':len(manifest['files']),'root_pins':len(sources),'reviewed_ranges':count,
        'compiler_jobs':0,'runtime_jobs':0,'new_theorems':0,'mandatory_source_stop':250,
        'one_hop_rank_unproved':True,'later_graph_rank_unproved':True,
        'authored_foundations_disclosed':True,
        'manifest_sha256':sha((HERE/'plan-manifest.json').read_bytes())},indent=2))

if __name__=='__main__':
    main()
