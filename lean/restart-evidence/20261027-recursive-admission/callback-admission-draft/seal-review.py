from pathlib import Path
import hashlib,json,datetime,shutil
base=Path('/tmp/mcfta-recursive-admission-20261027/callback-admission-draft');area=base.parent;repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
assert not (base/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest();now=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
name='SourcePruningEnumerationCallbackAdmission.lean';expected='bf5d79d4557b2a096906a3d4e9e98bed6c99a3900fc7a1fe3d13d0e26f7cc7cc';b=(repo/name).read_bytes()
for p in [base/name,base/'revisions/v1'/name,area/'strict-callback-admission-1/MicroCFTA'/name]:assert p.read_bytes()==b
assert sha(b)==expected
for d in ['sources','cuts','checked-source','evidence/strict-callback-admission-1','contracts']: (base/d).mkdir(parents=True,exist_ok=True)
(base/'checked-source'/name).write_bytes(b)
e=area/'strict-callback-admission-1';r=json.loads((e/'report.json').read_text());assert r['exit_code']==0 and r['bytes']==0 and r['source_sha256']==expected and (e/'raw.log').read_bytes()==b''
for f in ['report.json','raw.log']:shutil.copyfile(e/f,base/'evidence/strict-callback-admission-1'/f)
shutil.copyfile(e/'MicroCFTA'/name,base/'evidence/strict-callback-admission-1'/name)
specs=[
 (name,[(30,46),(52,77),(113,195)],'whole'),
 ('SourcePruningEnumerationHeadAdmission.lean',[(134,254)],'listed literal cut; original full contract and proof'),
 ('SourcePruningEnumerationFiniteCallbackReceiptLanguage.lean',[(41,71)],'listed literal cut'),
 ('SourcePruningEnumerationRecursiveReservation.lean',[(155,185)],'listed literal cut'),
 ('SourcePruningEnumerationFiniteReservation.lean',[(191,199),(273,284)],'listed literal cuts'),
 ('SourcePruningEnumerationNativeBranchCompletion.lean',[(31,56)],'listed literal cut'),
 ('EnumerationCompressionFrame.lean',[(19,34)],'listed literal cut'),
]
records=[]
for n,cuts,scope in specs:
 p=repo/n;whole=p.read_bytes();q=base/'sources'/n;q.write_bytes(whole)
 rec={'source':str(p),'snapshot':str(q),'scope':'whole custody copy','reviewed_scope':scope,'bytes':len(whole),'sha256':sha(whole),'cuts':[]}
 for first,last in cuts:
  cut=b''.join(whole.splitlines(keepends=True)[first-1:last]);dest=base/'cuts'/f'{n}.{first}-{last}.txt';dest.write_bytes(cut)
  rec['cuts'].append({'scope':'literal cut','first_line':first,'last_line':last,'snapshot':str(dest),'bytes':len(cut),'sha256':sha(cut)})
 records.append(rec)
(base/'source-index.json').write_text(json.dumps({'created':now,'cut_convention':'One-based inclusive line bounds; splitlines(keepends=True); trailing LF retained. Whole custody copy does not imply whole review when reviewed_scope lists cuts.','sources':records},indent=2)+'\n')
def decl(s,n):
 a=s.index('theorem '+n+'\n');return s[a:s.index(' := by',a)]
old=decl((repo/'SourcePruningEnumerationHeadAdmission.lean').read_text(),'head_finite_complete_resources_with_receipt')
new=decl(b.decode(),'head_finite_complete_resources_with_callback_admission')
renamed=old.replace('theorem head_finite_complete_resources_with_receipt\n','theorem head_finite_complete_resources_with_callback_admission\n',1)
last='      ∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),'
assert renamed.count(last)==1
grouped=renamed.replace(last,last.replace('      ∀','      (∀'),1)+')'
assert new.startswith(grouped+' ∧\n')
body=b.decode()[b.decode().index(' := by',b.decode().index('theorem head_finite_complete_resources_with_callback_admission\n')):]
assert body.count('head_finite_complete_resources_with_receipt ')==1
for file,txt in [('original-full-contract.txt',old),('new-full-contract.txt',new),('retained-old-grouped-contract.txt',grouped)]: (base/'contracts'/file).write_text(txt)
comparison={'created':now,'status':'PASS with exact necessary grouping','all_old_input_binders_unchanged':True,'all_old_existentials_and_field_bodies_unchanged':True,'raw_entire_declaration_prefix_identical':False,'reason':'The original final unparenthesized forall field is enclosed in parentheses before a separate appended conjunction. No field body changes.','transformation':'Rename theorem; insert one opening parenthesis immediately before original final forall and one closing parenthesis after its unchanged body; append new actual-complete admission field.','original_contract_bytes':len(old.encode()),'original_contract_sha256':sha(old.encode()),'original_producer_calls':1,'additional_initial_producer_premises':[]}
(base/'contract-comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
plan=area/'recursive-history-next-proof';pf=plan/'FROZEN.json';assert pf.exists()
(base/'closure-plan-reference.json').write_text(json.dumps({'created':now,'scope':'Previously frozen source-only closure plan; historical uncompiled status at its own creation is retained.','area':str(plan),'frozen_sha256':sha(pf.read_bytes()),'report':str(plan/'report.txt'),'report_sha256':sha((plan/'report.txt').read_bytes()),'current_update':'The callback-admission first step has since passed Root strict1 unchanged. It has not yet been threaded into old sibling or ordinary receipt families.'},indent=2)+'\n')
report=f'''[{now}] CLEAR — checked callback resource admission at the actual completed head.

The installed source, actual strict input, temp draft and preserved v1 are identical: 197 lines, 14032 bytes, SHA256 {expected}. Root's strict-callback-admission-1 records exit 0 and literal empty output under Lean 4.34.1, warningAsError and all linters. Its recorded memory.max/high are 4294967296 and swap limit is 0. Actual report, log and strict source are copied. No build was run for this review.

Public API. Recursive.RecursiveCallbackAdmission indexes the actual Inventory, Caller, full Memos, metadata, cache, target/fragment, recursive depth, original callback Seed and mass ceiling. Its fields retain Packet, FragmentBound, Fits, guard Heap, suspendedBound≤ceiling and finite Reserved. This is resource input data, not a successful callback or future semantic property. Target identity is an index; no extra target readiness claim is made by this structure.

RecursiveCallbackAdmission.after_false uses an actual FalseCallbackReceipt. Its returned Packet has the exact updated metadata and framed returned core. Frame.counter transports the actual fragment bound. Frame.values transports the original mass bound. Caller/full Memos/native heap, seed, ceiling, Fits, guard Heap and original reservation stay the same. Safe is retained from the actual returned Packet; it is not inferred from Frame. The theorem neither reconstructs a new reservation after execution nor asserts successful recursive continuation.

NativeHookResources.head_finite_complete_resources_with_callback_admission calls head_finite_complete_resources_with_receipt ONCE. It keeps every original input, witness and field body. The old terminal universal CompletedHeadReceipt field is enclosed in parentheses to append a separate actual-complete→admission field. This grouping is recorded explicitly: the raw entire declaration prefix is not byte-identical, while all original field bodies and binders are exact. No original conclusion is weakened or dropped. The full original stable runs, Post/full Memos, Admitted/Pending/FragmentHistory, HeadCacheBounds, Fits/Heap, unsupported-or-hook outcome packet and CompletedHeadReceipt remain.

Same actual completed endpoint. The new field takes receipt=.complete(fragment,reached,queries,after). The existing CompletedHeadReceipt supplies Packet at the SAME reached Caller/full middleMemos/cache. Admitted at that actual receipt supplies FragmentBound. The existing receipt's bounded/known fields supply Fits/Heap at RecursiveReservation.afterHead seed inherited. The seed and ceiling are fixed from original inputs before the receipt: callbackSeed=afterHead seed inherited; callbackCeiling=massCeil seed capturedMass inherited. The new field uses original HeadReserved.2 directly, without deriving reservation from the completed endpoint.

Exact cost and mass provenance. The retained old head producer derives actual edge child count and projected own-tries bounds from Packet.realized/Context, original Fits and guard Heap, using edge_shape_from_packet. edge_cost_le bounds the actual cost by edgeCount seed inherited. original reserved.edge supplies that genuine prefix reservation. head_complete_cache_bounds produces actual HeadCacheBounds and head endpoint Fits/Heap, which are padded to afterHead at the same original schedule. The new wrapper applies head_mass_le to this retained HeadCacheBounds plus initialMass and inheritedLength, then specializes it through the actual complete equation. It does not call the head producer again, assume a future cache, or infer mass from Safe alone.

Scope and remaining task. This closes the local omitted callback resource-admission export. It does NOT thread that new field through older InvocationReceipts or OrdinaryInvocationResources: those families still retain CompletedHeadReceipt alone. It does NOT strengthen Complete, enrich every recursive OutputHistory tag, or prove whole recursive backward assignment. The next concrete task is to thread this actual admission through stronger callback/head/sibling/ordinary producer variants and a stronger finite-depth IH. Richer stable bounds must be chosen before all universal actual work fuels. An old Complete bound is not assumed to dominate a separately chosen richer bound. The frozen recursive-history-next-proof bundle records the exact field requirements, parked route, same captured cache/full post-hook Memos and common-bound construction.

No finite corollary duplicates the large original contract. The existing original Complete theorem is already universally proved; the wrapper retains its unchanged abstract Complete input. No Canonical, semantic truth, desired assignment, future callback success or desired history is added to initial admission. There is no Safe assertion for rejected caches. No runtime, repository, old declarations or prior frozen evidence was changed by this draft/review.
'''
(base/'report.txt').write_text(report)
(base/'status.json').write_text(json.dumps({'created':now,'status':'Root strict1 PASS unchanged / CLEAR','source_sha256':expected,'original_revision':'v1','initial_draft_uncompiled_at_creation':True,'strict_family':str(e),'raw_bytes':0,'head_wrapper_producer_calls':1,'old_contract_grouping_explicit':True,'not_yet_threaded_to_sibling_ordinary_families':True,'report_sha256':sha(report.encode())},indent=2)+'\n')
for rec in records:
 whole=Path(rec['source']).read_bytes();assert sha(whole)==rec['sha256'] and whole==Path(rec['snapshot']).read_bytes()
 for c in rec['cuts']:
  cut=b''.join(whole.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert cut==Path(c['snapshot']).read_bytes() and sha(cut)==c['sha256']
files=sorted(p for p in base.rglob('*') if p.is_file() and p.name not in ['pins.json','FROZEN.json'])
pins={'created':now,'files':{str(p.relative_to(base)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files}}
(base/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
frozen={'created':now,'status':'FROZEN / CLEAR / actual Root strict1 PASS','payload_count':len(files),'exact_file_count':len(files)+2,'pins_sha256':sha((base/'pins.json').read_bytes()),'report_sha256':sha((base/'report.txt').read_bytes()),'source_index_sha256':sha((base/'source-index.json').read_bytes()),'source_sha256':expected,'contract_comparison_sha256':sha((base/'contract-comparison.json').read_bytes())}
(base/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
for rel,r in pins['files'].items(): x=(base/rel).read_bytes();assert len(x)==r['bytes'] and sha(x)==r['sha256']
assert len([p for p in base.rglob('*') if p.is_file()])==frozen['exact_file_count']
print(json.dumps({'area':str(base),'payload_count':len(files),'exact_file_count':len(files)+2,'FROZEN_sha256':sha((base/'FROZEN.json').read_bytes()),**{k:frozen[k] for k in ['pins_sha256','report_sha256','source_index_sha256','source_sha256']}},indent=2))
