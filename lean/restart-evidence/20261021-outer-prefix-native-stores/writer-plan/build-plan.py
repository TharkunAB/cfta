from pathlib import Path
import json,hashlib,shutil
root=Path('/home/tritlo/Code/mcfta')
here=Path('/tmp/mcfta-outer-resource-writers-next-plan')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
ranges={
'SourceCurrentResourceParentWriters':[(38,98),(126,250)],
'SourceCurrentOuterPrefixNativeStores':[(38,69),(140,198)],
'SourceCurrentOuterNativeStores':[(68,92),(250,285),(349,389),(459,528)],
'SourceCurrentOuterInitialActual':[(432,545)],
'SourceCurrentOuterInitialPrefix':[(38,86),(140,237),(264,288)],
'SourceCurrentOuterExecutionAncestry':[(326,375)],
'SourceCurrentOuterInitialSchedule':[(18,75),(123,153)],
'SourceCurrentOuterEdgeGuardAlphabet':[(103,166)],
'SourceCurrentInheritedNumeric':[(73,99)],
'SourceCurrentAllocatedPartialWorker':[(60,170)],
'SourceCurrentAllocatedPartialState':[(32,87),(104,138)],
'SourceCurrentAllocatedPartialGraph':[(32,42),(44,120)],
'SourceCurrentAllocatedPartialCallSteps':[(36,101)],
'SourceCurrentAllocatedPartialWorkerStability':[(24,39)],
'SourceCurrentOuterActiveAncestry':[(35,43)],
'SourceCurrentOuterPrefixInvariants':[(480,489)],
'SourceCurrentParentAlphabetReservation':[(45,109)],
'SourceCurrentConstrainedCapGeneratedQueryResources':[(34,73)],
'SourceCurrentAllocatedNativeResourceForecast':[(19,84)],
'SourceCurrentAllocatedPartialInvariant':[(26,67)],
}
pins=[]
for name,spans in ranges.items():
    path=f'lean/MicroCFTA/{name}.lean'; p=root/path
    target=here/'inputs/root'/path;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,target)
    lines=p.read_bytes().splitlines(keepends=True)
    checked=[]
    for lo,hi in spans:
        assert 1<=lo<=hi<=len(lines),(name,len(lines),lo,hi)
        checked.append({'start':lo,'end':hi,'sha256':hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()})
    pins.append({'path':path,'bytes':p.stat().st_size,'sha256':digest(p),'reviewed_ranges':checked})
write(here/'plan-source-pins.json',{'schema':1,'files':pins})
authorities={
'writer-owner-manifest.json':Path('/tmp/mcfta-resource-parent-writers-proof/resource-writers-manifest.json'),
'writer-owner-selection.json':Path('/tmp/mcfta-resource-parent-writers-proof/resource-writers-selection.json'),
'writer-independent-review-manifest.json':Path('/tmp/mcfta-resource-parent-writers-independent-review/review-manifest.json'),
'completed-store-owner-manifest.json':Path('/tmp/mcfta-outer-native-stores-proof/outer-native-stores-manifest.json'),
'completed-store-owner-selection.json':Path('/tmp/mcfta-outer-native-stores-proof/outer-native-stores-selection.json'),
'prefix-owner-manifest.json':Path('/tmp/mcfta-outer-prefix-native-stores-proof/prefix-native-stores-manifest.json'),
'prefix-owner-selection.json':Path('/tmp/mcfta-outer-prefix-native-stores-proof/prefix-native-stores-selection.json'),
'root-prefix-strict-1.json':root/'lean/restart-evidence/20261021-outer-prefix-native-stores/prefix-strict-1.json',
'root-prefix-audit-1.json':root/'lean/restart-evidence/20261021-outer-prefix-native-stores/audit-1.json',
}
for name,p in authorities.items():
    target=here/'inputs/authority'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,target)
prefix=Path('/tmp/mcfta-outer-prefix-native-stores-proof')
for stem in ['prefix-native-stores-direct-2','prefix-native-stores-public-1']:
    for ext in ['json','log','source.lean','limits.json','usage.json']:
        target=here/'inputs/prefix-checks'/f'{stem}.{ext}';target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(prefix/f'{stem}.{ext}',target)
shutil.copy2(prefix/'prefix-native-stores-public.lean',here/'inputs/prefix-checks/prefix-native-stores-public.lean')
selected={'schema':1,'status':'APPROVED SOURCE-ONLY PLAN; UNPROVED','public_head':'MicroCFTA.SourceCurrentOuterResourceWriters.reached','public_heads':1,'public_output':'SourceCurrentResourceParentWriters.Origins formulas solver (caller last)','new_lean_commands':0,'new_lake_commands':0,'new_canonical_commands':0,'new_public_pairs':0,'constructed_pairs':0,'official_edits':False,'implementation_requires_complete_source_review':True,'maximum_lines_before_review':650,'public_signature_sha256':digest(here/'proposed-signature.lean.txt'),'dependencies':{
'writer':{'source_sha256':'404f9ba2b58cbdb403608465e375d6f1af66686aaa3201288ba6ea219f75f4d2','owner_manifest_sha256':digest(here/'inputs/authority/writer-owner-manifest.json')},
'completed_stores':{'source_sha256':'b9f7f87df92990b460708bd71fb5f56085bc3b28b97c0a0d96ae1e12f6156f46','owner_manifest_sha256':digest(here/'inputs/authority/completed-store-owner-manifest.json')},
'prefix_stores':{'status':'FINAL FROZEN CHECKED; OFFICIAL ROOT STRICT AND AUDIT PASSED','source_sha256':'7e1d2349590e0cdd9ad3028e3b25ca1a2d44502766663551fcf901a185a4e1d8','owner_manifest_sha256':digest(here/'inputs/authority/prefix-owner-manifest.json'),'owner_selection_sha256':digest(here/'inputs/authority/prefix-owner-selection.json'),'selected_strict':'prefix-native-stores-direct-2','selected_public':'prefix-native-stores-public-1','copied_selected_lean_commands':2}},'authored_foundations':['MicroCFTA.SourceCurrentOuterNativeStores','MicroCFTA.SourceCurrentActualParentScanNativeStores','transitive native position, scope and corridor foundations'],'missing_mathematical_contracts':[]}
write(here/'plan-selection.json',selected)
plan=(here/'plan.md').read_text()
plan=plan.replace('The prefix-store dependency must have an actual selected pass before implementation uses it; final dependency status and exact artifacts are pinned.','The prefix-store dependency is now frozen at 198 lines, SHA256 7e1d2349590e0cdd9ad3028e3b25ca1a2d44502766663551fcf901a185a4e1d8. Selected strict2 and FULL1 pass. The exact official source also passed root strict and full Audit. The plan pins these actual selected artifacts and final metadata; it no longer treats this API as a pending proposal.')
(here/'plan.md').write_text(plan)
print(len(pins),'source pins')
