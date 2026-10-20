import hashlib,json,re,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def read(name):return json.loads((HERE/name).read_text())
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
module='SourceCurrentNativeOriginalCapturedNodeRows'
proof=(HERE/'proof-commit.txt').read_text().strip()
assert proof=='de1791f450e99f036ce0e29ef4bcb5b7c16b12fb'
write('selected-strict.json',{module:'root-captured-strict-1'})
write('selected-canonical.json',{module:'root-captured-canonical-1'})
write('selected-canonical-warnings.json',{module:re.findall(r'^warning:.*$',(HERE/'root-captured-canonical-1.log').read_text(),re.M)})
fixture=read('capture-fixture/captured-node-rows-kernels-selection.json');assert fixture['finalized']
fixture_group=fixture['groups'][0];assert fixture_group['pairs']==1 and fixture_group['full_proof']
write('selected-groups.json',[dict(name='capture-module/captured-node-rows-public-1',pairs=1,kind='new-public',full_proof=True),dict(name='capture-fixture/'+fixture_group['name'],pairs=1,kind='constructed',full_proof=True)])
write('selected-constructed-strict.json',{'root-captured-fixture-strict-1':'capture-fixture/captured-node-rows-kernels.lean'})
log=(HERE/'root-captured-audit-1.log').read_text()
jobs=int(re.findall(r'Build completed successfully \((\d+) jobs\)',log)[-1]);deps=int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',log)[-1]);assert (jobs,deps)==(3540,74337)
write('selected-audit.json',dict(name='root-captured-audit-1',jobs=jobs,dependency_checks=deps,root_observed_handle=73837,root_observed_terminal_exit=0))
write('expected-counts.json',dict(modules=1,pairs={'new-public':1,'constructed':1,'private-claim':0},constructed_strict=1,audit_jobs=jobs,audit_dependency_checks=deps))
heads=['MicroCFTA.'+module+'.'+name for name in re.findall(r'^(?:theorem|def|structure|inductive) ([A-Za-z0-9_.]+)',(ROOT/'lean/MicroCFTA'/(module+'.lean')).read_text(),re.M)];assert heads==['MicroCFTA.'+module+'.capture_node_rows'];write('public-heads.json',heads)
write('component-verifiers.json',[
 dict(path='capture-module/captured-node-rows-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='unfold-core/unfold-node-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='source-review/math-review-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='capture-fixture/captured-node-rows-kernels-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='fixture-review/fixture-review-verify.py',arguments=['--live','--root',str(ROOT),'--fixture',str(HERE/'capture-fixture')])])
verifiers=read('component-verifiers.json');verifiers.append({'path': 'next-generated-capture/plan-verify.py', 'arguments': ['--live', '--root', '/home/tritlo/Code/mcfta']});write('component-verifiers.json',verifiers)
unique={};diagnostics={}
for path in HERE.rglob('*.json'):
 try:data=json.loads(path.read_text())
 except ValueError:diagnostics[str(path.relative_to(HERE))]=hashlib.sha256(path.read_bytes()).hexdigest();continue
 if (isinstance(data,dict) and isinstance(data.get('command'),list) and isinstance(data.get('exit_code'),int) and 'wrapper' in data and Path(data['command'][0]).name in ['lean','lake']):unique.setdefault(json.dumps(data,sort_keys=True),[]).append(str(path.relative_to(HERE)))
write('non-json-evidence.json',diagnostics)
write('attempt-accounting.json',dict(capped_commands=len(unique),failed_commands=sum(json.loads(key)['exit_code']!=0 for key in unique),commands=[dict(receipts=paths,exit_code=json.loads(key)['exit_code']) for key,paths in unique.items()],receipt_copies_add_commands=False,selected_constructed_examples=1,constructed_family='The existing distinct-used-outer/shared-used-inner source family; actual native prefix and changed-child unfold force actual Calls for the same stored-row original node producer. No new source family.',auxiliary_helper_readbacks=0))
strict=read('root-captured-fixture-strict-1.json');assert strict['exit_code']==0 and not (HERE/'root-captured-fixture-strict-1.log').read_bytes()
write('selection-status.json',dict(finalized=True,public_pairs=1,constructed_pairs=1,root_fixture_observed_handle=int(sys.argv[1]),root_fixture_observed_terminal_exit=0,root_fixture_sha256=strict['sha256'],root_module_observed_strict_handle=None,root_module_observed_canonical_handle=3496,root_final_audit_observed_handle=73837,root_final_audit_observed_terminal_exit=0))
write('goal-turn.json',dict(classification='progress',goal_status='active',prior_checkpoint='499357bf4fe4bc50c9183271f028dd43d21e475e',proof_commit=proof,new_route='One actual checked native capture splits initial and generated Mu cells. The exact initial full cell fixes one indexed original publication before all stored rows and actual successful unfolds. Derived current support yields stored-row anchors, actual changed-child Calls and same-trace ultimate original node RowCalls for those stored anchors.',interface_limit='Initial captures now retain indexed original node production for stored rows and actual successful unfold anchors. Generated captures, residual observations, global owner renewal and Haskell refinement remain open.',remaining=['generated-capture original ancestry','residual Mu observations','global renewal and active-owner exclusion','final owner retention','outer completion and convergence','Haskell refinement'],counts_are_not_completion_measure=True))
write('current-documents.json',['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md','lean/notes-current-native-original-captured-node-rows.md','lean/MicroCFTA/Audit.lean'])
print(json.dumps(dict(status='PASS',public_heads=len(heads),capped_commands=len(unique),failed_commands=sum(json.loads(key)['exit_code']!=0 for key in unique))))
