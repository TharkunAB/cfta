from pathlib import Path
import hashlib
import json
import shutil

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
def sha(data):
    return hashlib.sha256(data).hexdigest()
def write(name,value):
    (HERE/name).write_text(json.dumps(value,indent=2)+'\n')

specs={
    'SourceCurrentOuterInitialBusy.lean':[(32,87)],
    'SourceCurrentOuterExecutionAncestry.lean':[(25,28),(461,495),(695,720)],
    'SourceCurrentOuterPrefixInvariants.lean':[(549,559),(646,667)],
    'SourceCurrentAllocatedPartialState.lean':[(59,61),(89,107),(157,162)],
    'FlatMemoThunkReturned.lean':[(72,79)],
    'SourceCurrentOuterActiveAncestry.lean':[(245,252)],
    'SourceCurrentOuterEdgeIdle.lean':[(23,42),(232,276)],
    'SourceCurrentOlderOwnerLineage.lean':[(95,124)],
}
pins=[]
for name,ranges in specs.items():
    relative='lean/MicroCFTA/'+name
    data=(ROOT/relative).read_bytes()
    target=HERE/'sourcepins'/name
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(data)
    lines=data.splitlines(keepends=True)
    intervals=[]
    for first,last in ranges:
        assert 0<first<=last<=len(lines),(name,first,last,len(lines))
        part=b''.join(lines[first-1:last])
        snapshot=f'ranges/{name}.{first}-{last}.txt'
        (HERE/snapshot).parent.mkdir(exist_ok=True)
        (HERE/snapshot).write_bytes(part)
        intervals.append({'first':first,'last':last,'snapshot':snapshot,'sha256':sha(part)})
    pins.append({'root_path':relative,'snapshot':'sourcepins/'+name,
        'sha256':sha(data),'bytes':len(data),'reviewed_ranges':intervals})
write('sourcepins.json',{'pins':pins})
body=Path('/tmp/mcfta-older-owner-lineage-proof')
(HERE/'inputs').mkdir(exist_ok=True)
for source,target in [
    ('SourceCurrentOlderOwnerLineage.lean','body-source.lean.txt'),
    ('older-owner-lineage-direct-2.json','body-selected-strict.json'),
    ('older-owner-lineage-direct-2.log','body-selected-strict.log'),
    ('older-owner-lineage-public-1.json','body-selected-public.json'),
    ('older-owner-lineage-readback.json','body-readback.json'),
    ('older-owner-lineage-manifest.json','body-owner-manifest.json'),
    ('older-owner-lineage-selection.json','body-owner-selection.json')]:
    shutil.copyfile(body/source,HERE/'inputs'/target)
write('dependency-readiness-cue.json',{
    'time':'2026-10-21 12:25 CEST',
    'historical_approved_plan_unchanged':True,
    'body_source_sha256':'d6653bb67934bf1158124417013738b679735c49c057381510909052ca6cd41e',
    'body_author_selected_strict':'terminal0; raw empty',
    'body_author_FULL':'terminal0; complete4762369bytes; standard3; type identity',
    'body_root_strict':'personally terminal0; raw empty',
    'body_owner_frozen_manifest_sha256':'d76d273c4e96d8a4160ae32591a036c2bb912b1d953da88904a06f89ed748dd0',
    'body_official_installed':True,
    'body_Audit_and_compiled_artifact_readiness':'Audit compiling at cue; root-owned and not claimed ready',
    'dependency_checks_reused_as_status_evidence':True,
    'this_plan_did_not_launch_or_independently_repeat_dependency_checks':True})
write('status.json',{'source_only':True,'compiler_jobs':0,'runtime_jobs':0,
    'canonical_jobs':0,'new_theorems':0,'implementation_included':False,
    'no_node_busy':'unproved proposed consumer','initial_node_idle_required':True,
    'edge_busy_scope':'existing separate EdgeIdle producers',
    'finite_renewals_and_completion':'unproved and outside this component',
    'authored_foundations_disclosed':True})
write('selection.json',{'finalized':True,'source_reviewed':True,'elaborated':False,
    'implementation_authorized_by_this_package':False,
    'plan_sha256':sha((HERE/'plan.md').read_bytes()),
    'signature_sha256':sha((HERE/'proposed-signature.lean.txt').read_bytes()),
    'public_heads':['MicroCFTA.SourceCurrentOlderOwnerBusy.no_node_busy'],
    'root_and_guard_complete_plan_clearance':'2026-10-21 12:24 CEST'})
excluded={'plan-manifest.json','verification.json','live-verification.json'}
files=[]
for path in sorted(HERE.rglob('*')):
    if path.is_file() and path.name not in excluded:
        data=path.read_bytes()
        files.append({'path':str(path.relative_to(HERE)),'bytes':len(data),'sha256':sha(data)})
write('plan-manifest.json',{'finalized':True,'files':files})
