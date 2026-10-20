import hashlib,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def read(name):return json.loads((HERE/name).read_text())
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
module='SourceCurrentNativeOriginalPublicationTrace'
proof=(HERE/'proof-commit.txt').read_text().strip()
assert proof=='def05b051f229383856dd88fecc29c0a14743fd3'
write('selected-strict.json',{module:'root-trace-strict-1'})
write('selected-canonical.json',{module:'root-trace-canonical-1'})
write('selected-canonical-warnings.json',{module:re.findall(r'^warning:.*$',(HERE/'root-trace-canonical-1.log').read_text(),re.M)})
fixture=read('trace-fixture/publication-trace-kernels-selection.json')
assert fixture['finalized']
fixture_group=fixture['groups'][0]
assert fixture_group['pairs']==1 and fixture_group['full_proof']
write('selected-groups.json',[
 dict(name='trace-module/publication-trace-public-1',pairs=2,kind='new-public',full_proof=True),
 dict(name='trace-fixture/'+fixture_group['name'],pairs=1,kind='constructed',full_proof=True)])
write('selected-constructed-strict.json',{'root-trace-fixture-strict-1':'trace-fixture/publication-trace-kernels.lean'})
log=(HERE/'root-trace-audit-1.log').read_text()
jobs=int(re.findall(r'Build completed successfully \((\d+) jobs\)',log)[-1])
deps=int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',log)[-1])
assert (jobs,deps)==(3537,74326)
write('selected-audit.json',dict(name='root-trace-audit-1',jobs=jobs,dependency_checks=deps,root_observed_handle=11722,root_observed_terminal_exit=0))
write('expected-counts.json',dict(modules=1,pairs={'new-public':2,'constructed':1,'private-claim':0},constructed_strict=1,audit_jobs=jobs,audit_dependency_checks=deps))
heads=['MicroCFTA.'+module+'.'+name for name in re.findall(r'^(?:theorem|def|structure|inductive) ([A-Za-z0-9_.]+)',(ROOT/'lean/MicroCFTA'/(module+'.lean')).read_text(),re.M)]
assert heads==['MicroCFTA.'+module+'.'+name for name in ['events','build_trace_writers']]
write('public-heads.json',heads)
write('component-verifiers.json',[
 dict(path='trace-module/publication-trace-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='order-helpers/order-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='source-review/math-review-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='trace-fixture/publication-trace-kernels-verify.py',arguments=['--live','--root',str(ROOT)]),
 dict(path='fixture-review/fixture-review-verify.py',arguments=['--live','--root',str(ROOT),'--fixture',str(HERE/'trace-fixture')]),
 dict(path='next-resumption-plan/plan-verify.py',arguments=['--live','--root',str(ROOT)])])
unique={}; diagnostics={}
for path in HERE.rglob('*.json'):
 try:data=json.loads(path.read_text())
 except ValueError:
  diagnostics[str(path.relative_to(HERE))]=hashlib.sha256(path.read_bytes()).hexdigest();continue
 if (isinstance(data,dict) and isinstance(data.get('command'),list) and isinstance(data.get('exit_code'),int) and 'wrapper' in data and Path(data['command'][0]).name in ['lean','lake']):
  unique.setdefault(json.dumps(data,sort_keys=True),[]).append(str(path.relative_to(HERE)))
write('non-json-evidence.json',diagnostics)
write('attempt-accounting.json',dict(capped_commands=len(unique),failed_commands=sum(json.loads(key)['exit_code']!=0 for key in unique),commands=[dict(receipts=paths,exit_code=json.loads(key)['exit_code']) for key,paths in unique.items()],receipt_copies_add_commands=False,selected_constructed_examples=1,constructed_family='The same box[nested,outer] source family; this version derives strict earlier indices in the one returned trace.',auxiliary_helper_readbacks_not_official_pairs=3))
strict=read('root-trace-fixture-strict-1.json');assert strict['exit_code']==0 and not (HERE/'root-trace-fixture-strict-1.log').read_bytes()
write('selection-status.json',dict(finalized=True,public_pairs=2,constructed_pairs=1,root_fixture_observed_handle=int(sys.argv[1]),root_fixture_observed_terminal_exit=0,root_fixture_sha256=strict['sha256'],root_module_observed_strict_handle=48665,root_module_observed_canonical_handle=74346,root_final_audit_observed_handle=11722,root_final_audit_observed_terminal_exit=0))
write('goal-turn.json',dict(classification='progress',goal_status='active',prior_checkpoint='cf36913f01e73dc3a9dc76fbac3e52d7b90823bb',proof_commit=proof,new_route='One actual rooted build path gives a common postorder trace. Both final full-cell writers and strictly earlier precompletion writers retain membership, exact payload, original Reached, prefix, three callback paths and physical/issued suffixes in that same trace. The warm source derives an actual earlier full cell at the recovered outer callback and obtains two strict indexed events.',interface_limit='Source publication chronology still requires fixed-event row and resumption consumers. It is not a global rank over generated native owner renewal.',remaining=['fixed-event resumption ancestry','generated-capture original ancestry','residual Mu observations','global renewal and active-owner exclusion','final owner retention','outer completion and convergence','Haskell refinement'],counts_are_not_completion_measure=True))
write('current-documents.json',['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md','lean/notes-current-native-original-publication-trace.md','lean/MicroCFTA/Audit.lean'])
print(json.dumps(dict(status='PASS',public_heads=len(heads),capped_commands=len(unique),failed_commands=sum(json.loads(key)['exit_code']!=0 for key in unique))))
