from pathlib import Path
import hashlib
import json
import shutil

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

specs = {
    'SourceCurrentResourceOwnerInheritedDispatch.lean': [(29,56),(60,157)],
    'SourceCurrentResourceOwnerInheritedProgress.lean': [(35,76)],
    'SourceCurrentPositiveQuotientCount.lean': [(123,193)],
    'SourceCurrentResourceParentPositiveBack.lean': [(60,208)],
    'SourceCurrentResourceParentWriters.lean': [(64,85),(159,248)],
    'SourceCurrentOuterInitialPrefix.lean': [(264,286)],
    'SourceCurrentOuterPrefixNativeStores.lean': [(160,196)],
    'SourceCurrentOuterResourceWriters.lean': [(437,463)],
    'SourceCurrentOuterUntouchedProgress.lean': [(46,79)],
    'SourceCurrentOuterInitialActual.lean': [(526,545)],
    'SourceCurrentOuterInitialSchedule.lean': [(1,153)],
    'SourceCurrentConjunctionEquality.lean': [(86,104)],
    'SourceCurrentOuterOriginDependencies.lean': [(83,117)],
    'SourceCurrentAllocatedInheritedPrefix.lean': [(29,84)],
    'SourceCurrentAllocatedPartialGraph.lean': [(33,42)],
    'SourceEqualityConstraintMemoAllocation.lean': [(313,324)],
    'SourceEqualityDescend.lean': [(17,34)],
    'SourceCurrentAllocatedPartialReturnedDomain.lean': [(26,28)],
    'InternedValueMass.lean': [(17,49),(109,127)],
    'SourceMemoGate.lean': [(23,26)],
    'SourceCurrentAllocatedPartialWorker.lean': [(134,170)],
}
pins = []
for name, ranges in specs.items():
    relative = 'lean/MicroCFTA/' + name
    data = (ROOT / relative).read_bytes()
    target = HERE / 'sourcepins' / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    lines = data.splitlines(keepends=True)
    intervals = []
    for first,last in ranges:
        assert 0 < first <= last <= len(lines), (name, first, last, len(lines))
        content = b''.join(lines[first-1:last])
        snapshot = f'ranges/{name}.{first}-{last}.txt'
        (HERE / snapshot).parent.mkdir(exist_ok=True)
        (HERE / snapshot).write_bytes(content)
        intervals.append({'first':first,'last':last,'snapshot':snapshot,'sha256':sha(content)})
    pins.append({'root_path':relative,'snapshot':'sourcepins/'+name,
        'sha256':sha(data),'bytes':len(data),'reviewed_ranges':intervals})
write('sourcepins.json', {'pins':pins})
for source, target in [
    ('/tmp/mcfta-any-child-positive-back-next-plan/proposed-signature.lean.txt','inputs/back-proposed-signature.lean.txt'),
    ('/tmp/mcfta-resource-parent-positive-back-proof/resource-parent-positive-back-manifest.json','inputs/back-owner-manifest.json'),
    ('/tmp/mcfta-resource-parent-positive-back-proof/resource-parent-positive-back-selection.json','inputs/back-owner-selection.json'),
    ('/tmp/mcfta-positive-quotient-count-proof/positive-quotient-count-manifest.json','inputs/count-owner-manifest.json'),
    ('/tmp/mcfta-positive-quotient-count-proof/positive-quotient-count-selection.json','inputs/count-owner-selection.json')]:
    (HERE / target).parent.mkdir(exist_ok=True)
    shutil.copyfile(source, HERE / target)
write('checked-dependency-cue.json', {
    'time':'2026-10-21 11:55 CEST',
    'historical_plan_status_preserved':True,
    'back_source':'fa63f2d89d8494b24e5563bff710f4d9eab9b887a951ee16a1ab28660c04fc7e',
    'back_author_strict_and_full':'passed; two commands, zero failures',
    'back_official_installed':True,
    'back_root_strict':'passed',
    'back_audit_and_artifact_readiness':'root-owned; Audit running at cue',
    'this_package_compiler_jobs':0,
    'this_package_does_not_authorize_compiler':True})
write('status.json', {'source_only':True,'compiler_jobs':0,'runtime_jobs':0,
    'canonical_jobs':0,'new_theorems':0,'counterexample_executions':0,
    'implementation_included':False,'rank_theorem':'unproved proposed one-hop consumer',
    'later_graph_rank':'unproved separate target','mandatory_source_stop':250,
    'stop_before_compiler_and_further_machinery':True,
    'no_active_owner_premise':True,'authored_foundations_disclosed':True})
write('selection.json', {'finalized':True,'source_reviewed':True,'elaborated':False,
    'implementation_authorized_by_this_package':False,
    'plan_sha256':sha((HERE/'plan.md').read_bytes()),
    'signature_sha256':sha((HERE/'proposed-signature.lean.txt').read_bytes()),
    'public_heads':['MicroCFTA.SourceCurrentActualChildRank.dispatch'],
    'root_and_guard_complete_plan_clearance':'2026-10-21 11:55 CEST'})
excluded = {'plan-manifest.json','verification.json','live-verification.json'}
files = []
for path in sorted(HERE.rglob('*')):
    if path.is_file() and path.name not in excluded:
        data=path.read_bytes()
        files.append({'path':str(path.relative_to(HERE)),'bytes':len(data),'sha256':sha(data)})
write('plan-manifest.json', {'finalized':True,'files':files})
