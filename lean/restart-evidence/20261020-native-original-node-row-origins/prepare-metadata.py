import hashlib,json,re,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def read(name):return json.loads((HERE/name).read_text())
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
module='SourceCurrentNativeOriginalNodeRowOrigins'
proof=(HERE/'proof-commit.txt').read_text().strip()
assert proof=='6489bddee3161ef38e2d74008f8877cc00fdcde9'
write('selected-strict.json',{module:'root-node-strict-1'})
write('selected-canonical.json',{module:'root-node-canonical-1'})
write('selected-canonical-warnings.json',{module:re.findall(r'^warning:.*$',(HERE/'root-node-canonical-1.log').read_text(),re.M)})
fixture=read('node-fixture/node-row-origins-kernels-selection.json');assert fixture['finalized']
fixture_group=fixture['groups'][0];assert fixture_group['pairs']==1 and fixture_group['full_proof']
write('selected-groups.json',[dict(name='node-module/node-row-origins-public-1',pairs=1,kind='new-public',full_proof=True),dict(name='node-fixture/'+fixture_group['name'],pairs=1,kind='constructed',full_proof=True)])
write('selected-constructed-strict.json',{'root-node-fixture-strict-1':'node-fixture/node-row-origins-kernels.lean'})
log=(HERE/'root-node-audit-1.log').read_text()
jobs=int(re.findall(r'Build completed successfully \((\d+) jobs\)',log)[-1]);deps=int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',log)[-1]);assert (jobs,deps)==(3539,74335)
write('selected-audit.json',dict(name='root-node-audit-1',jobs=jobs,dependency_checks=deps,root_observed_handle=86135,root_observed_terminal_exit=0))
write('expected-counts.json',dict(modules=1,pairs={'new-public':1,'constructed':1,'private-claim':0},constructed_strict=1,audit_jobs=jobs,audit_dependency_checks=deps))
heads=['MicroCFTA.'+module+'.'+name for name in re.findall(r'^(?:theorem|def|structure|inductive) ([A-Za-z0-9_.]+)',(ROOT/'lean/MicroCFTA'/(module+'.lean')).read_text(),re.M)];assert heads==['MicroCFTA.'+module+'.build_node_row_origins'];write('public-heads.json',heads)
write('component-verifiers.json',[
 dict(path='node-module/node-row-origins-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='source-review/math-review-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='node-fixture/node-row-origins-kernels-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='fixture-review/fixture-review-verify.py',arguments=['--live','--root',str(ROOT),'--fixture',str(HERE/'node-fixture')])])
unique={};diagnostics={}
for path in HERE.rglob('*.json'):
 try:data=json.loads(path.read_text())
 except ValueError:diagnostics[str(path.relative_to(HERE))]=hashlib.sha256(path.read_bytes()).hexdigest();continue
 if (isinstance(data,dict) and isinstance(data.get('command'),list) and isinstance(data.get('exit_code'),int) and 'wrapper' in data and Path(data['command'][0]).name in ['lean','lake']):unique.setdefault(json.dumps(data,sort_keys=True),[]).append(str(path.relative_to(HERE)))
write('non-json-evidence.json',diagnostics)
write('attempt-accounting.json',dict(capped_commands=len(unique),failed_commands=sum(json.loads(key)['exit_code']!=0 for key in unique),commands=[dict(receipts=paths,exit_code=json.loads(key)['exit_code']) for key,paths in unique.items()],receipt_copies_add_commands=False,selected_constructed_examples=1,constructed_family='The same box[nested,outer] source family; this version reaches the actual node producer and derives a strict index jump.',auxiliary_helper_readbacks=0))
strict=read('root-node-fixture-strict-1.json');assert strict['exit_code']==0 and not (HERE/'root-node-fixture-strict-1.log').read_bytes()
write('selection-status.json',dict(finalized=True,public_pairs=1,constructed_pairs=1,root_fixture_observed_handle=int(sys.argv[1]),root_fixture_observed_terminal_exit=0,root_fixture_sha256=strict['sha256'],root_module_observed_strict_handle=58371,root_module_observed_canonical_handle=78150,root_final_audit_observed_handle=86135,root_final_audit_observed_terminal_exit=0))
write('goal-turn.json',dict(classification='progress',goal_status='active',prior_checkpoint='d425c2942983129a513d44dcaa196a3f44d7b87b',proof_commit=proof,new_route='One actual original build fixes a common publication path. Strong induction on the same publication index eliminates every repeated binder stop for the same complete stored row and returns an actual original node SourceRow/build/RowCall with same-row equality, original rooted Context, producer-relative syntax bound, same-trace producer index and forward physical/issued suffix.',interface_limit='Original stored-row ultimate node ancestry is proved. Actual native captures, generated events and global owner renewal still need correspondence and progress.',remaining=['actual initial capture and unfold correspondence','generated-capture original ancestry','residual Mu observations','global renewal and active-owner exclusion','final owner retention','outer completion and convergence','Haskell refinement'],counts_are_not_completion_measure=True))
write('current-documents.json',['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md','lean/notes-current-native-original-node-row-origins.md','lean/MicroCFTA/Audit.lean'])
print(json.dumps(dict(status='PASS',public_heads=len(heads),capped_commands=len(unique),failed_commands=sum(json.loads(key)['exit_code']!=0 for key in unique))))
