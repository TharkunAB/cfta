from pathlib import Path
import hashlib,json,difflib,datetime,shutil
base=Path('/tmp/mcfta-recursive-history-resources-20261027/history-contract-draft');area=base.parent;repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
assert not (base/'FROZEN.json').exists()
for d in ['sources','cuts','contracts','checked-source','evidence','revisions/root-v3']: (base/d).mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest();now=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
specs=[
 ('SourcePruningEnumerationFiniteContract.lean',[(28,48)]),
 ('SourcePruningEnumerationOutputHistory.lean',[(27,70),(102,170)]),
 ('SourcePruningEnumerationCallbackAdmission.lean',[(30,77)]),
 ('SourcePruningEnumerationFiniteCallbackResources.lean',[(38,116)]),
 ('SourcePruningEnumerationRecursiveCallback.lean',[(29,61)]),
 ('SourcePruningEnumerationZeroOutcomeResources.lean',[(24,60)]),
 ('SourcePruningEnumerationHeadAdmission.lean',[(71,102)]),
]
index=[]
for name,cuts in specs:
 p=repo/name;b=p.read_bytes();q=base/'sources'/name;q.write_bytes(b)
 rec={'source':str(p),'snapshot':str(q),'scope':'whole source custody copy','reviewed_scope':'listed literal cuts','bytes':len(b),'sha256':sha(b),'cuts':[]}
 for f,l in cuts:
  cut=b''.join(b.splitlines(keepends=True)[f-1:l]);d=base/'cuts'/f'{name}.{f}-{l}.txt';d.write_bytes(cut)
  rec['cuts'].append({'scope':'literal cut','first_line':f,'last_line':l,'snapshot':str(d),'bytes':len(cut),'sha256':sha(cut)})
 index.append(rec)
(base/'source-index.json').write_text(json.dumps({'created':now,'cut_convention':'One-based inclusive lines; source.read_bytes().splitlines(keepends=True)[first_line-1:last_line]. Preserve LF. Whole custody copies do not imply full review when reviewed_scope says cuts.','sources':index},indent=2)+'\n')
name='SourcePruningEnumerationFiniteHistoryContract.lean';old=(base/'revisions/v2'/name).read_text();checked=(repo/name).read_text();r=json.loads((area/'strict-history-contract-2/report.json').read_text());assert r['exit_code']==0 and r['bytes']==0 and r['source_sha256']==sha(checked.encode());assert checked==(area/'strict-history-contract-2/MicroCFTA'/name).read_text()
assert checked==old.replace('        rw [chosen]\n        exact .stopped admission','        exact .stopped admission').replace('            rw [chosen]\n            exact .done admission','            exact .done admission')
(base/'checked-source'/name).write_text(checked);(base/'revisions/root-v3'/name).write_text(checked)
forward=''.join(difflib.unified_diff(old.splitlines(keepends=True),checked.splitlines(keepends=True),fromfile='v2/'+name,tofile='root-v3/'+name));inverse=''.join(difflib.unified_diff(checked.splitlines(keepends=True),old.splitlines(keepends=True),fromfile='root-v3/'+name,tofile='v2/'+name))
(base/'revisions/root-v3/forward.patch').write_text(forward);(base/'revisions/root-v3/inverse.patch').write_text(inverse)
ops=[]
for tag,a,b,c,d in difflib.SequenceMatcher(a=old,b=checked,autojunk=False).get_opcodes():
 if tag!='equal':ops.append({'old_start':a,'old_end':b,'old_text':old[a:b],'new_start':c,'new_end':d,'new_text':checked[c:d]})
rebuilt=old
for op in reversed(ops):assert rebuilt[op['old_start']:op['old_end']]==op['old_text'];rebuilt=rebuilt[:op['old_start']]+op['new_text']+rebuilt[op['old_end']:]
assert rebuilt==checked
back=checked
for op in reversed(ops):assert back[op['new_start']:op['new_end']]==op['new_text'];back=back[:op['new_start']]+op['old_text']+back[op['new_end']:]
assert back==old
(base/'revisions/root-v3/recipe.json').write_text(json.dumps({'created':now,'index_units':'Unicode code points; Python string indices; end exclusive; apply in descending starts','before_sha256':sha(old.encode()),'after_sha256':sha(checked.encode()),'bidirectional_reconstruction':True,'spans':ops},indent=2,ensure_ascii=False)+'\n')
for fam in ['strict-history-contract-1','strict-history-contract-2']:
 e=area/fam;d=base/'evidence'/fam;d.mkdir(exist_ok=True)
 for f in ['report.json','raw.log']:shutil.copyfile(e/f,d/f)
 shutil.copyfile(e/'MicroCFTA'/name,d/name)
# Literal contract retention for Complete and the concrete callback.
original=(base/'sources/SourcePruningEnumerationFiniteContract.lean').read_text();a=original.index('def Complete\n');oldContract=original[a:original.index('\n\nend ',a)]
new=(base/'SourcePruningEnumerationFiniteHistoryContract.lean').read_text();a=new.index('def CompleteWithHistory\n');newContract=new[a:new.index('/-- Forgetting history',a)].rstrip()
renamed=oldContract.replace('def Complete\n','def CompleteWithHistory\n',1);assert newContract.startswith(renamed+' ∧\n')
oldCallback=(base/'sources/SourcePruningEnumerationFiniteCallbackResources.lean').read_text();a=oldCallback.index('theorem callback_finite_complete_resources\n');oldCallback=oldCallback[a:oldCallback.index(' := by',a)]
newCallback=(base/'SourcePruningEnumerationFiniteCallbackHistory.lean').read_text();a=newCallback.index('theorem callback_finite_complete_resources_with_history\n');b=newCallback.index(' := by',a);newCallbackContract=newCallback[a:b]
renamedCallback=oldCallback.replace('theorem callback_finite_complete_resources\n','theorem callback_finite_complete_resources_with_history\n',1).replace('(recursive : Complete (bits := bits)','(recursive : CompleteWithHistory (bits := bits)',1)
assert newCallbackContract.startswith(renamedCallback+' ∧\n');callbackBody=newCallback[b:];assert callbackBody.count('callback_complete ')==1 and callbackBody.count(' := recursive\n')==1
for name,text in [('old-complete.txt',oldContract),('new-complete-with-history.txt',newContract),('old-finite-callback.txt',oldCallback),('new-finite-callback-with-history.txt',newCallbackContract)]: (base/'contracts'/name).write_text(text)
(base/'contract-comparison.json').write_text(json.dumps({'created':now,'status':'literal PASS','complete_input_result_prefix_retained':True,'complete_only_changes':'Definition name, then appended ResourceHistory field after original running and OutcomeResources.','forget_same_witnesses':'The proof calls CompleteWithHistory once and returns its exact bound/outcome/running/resources.','callback_old_prefix_retained':True,'callback_only_input_change':'Abstract smaller-depth IH changes Complete to CompleteWithHistory. All runtime/resource admission arguments remain unchanged.','callback_recording_producer_calls':1,'stronger_recursive_IH_calls_in_false_branch':1,'callback_uniform_bound':'callbackFuel+resumeFuel chosen before all extra/output quantifiers.','unproved_positive_depth_closure':True},indent=2)+'\n')
(base/'preparation-report.txt').write_text(f'''[{now}] Submitted bounded source drafts; not yet a final seal.

The checked contract root-v3 passes strict-history-contract-2 with empty raw output, SHA256 {sha(checked.encode())}. V1 (without the later requested full local head receipt), rich-head V2 and checked root-v3 are all retained. Root-v3 removes only two redundant rw[chosen] steps after cases already rewrites the stop/done target. Both failed strict1 and successful strict2 exact source/log/report records are copied. The top-level contract draft remains the exact rich-head V2 submission; checked-source is the authoritative checked variant.

FiniteHistoryContract defines current HistoryAdmission, exact OrdinaryHistoryReceipt, inductive ResourceHistory and CompleteWithHistory. All actual operation equations remain. OrdinaryHistoryReceipt retains the actual entry singleton at W, SAME entered cache, narrowed and entered full Packets, aggregate ordinary-to-local-head Post with full Memos, actual captured completion at W and the full CompletedHeadReceipt at its local bound. ResourceHistory ordinary retains the original-to-ordinary prefix Post, callback input admission and the smaller-depth tail at the same returned Inventory/full Memos/framed cache/seed/ceiling. Bare done or stopped tags do not imply Discharged.

CompleteWithHistory has the full original universal input sequence and original stable output/resource prefix literally, followed by admitted histories at bound+extra. Its forget theorem returns that same bound/outcome. The zero base uses actual resume_zero_outcome_resources. It constructs actual stop/done history tags and excludes outputs from stuck/zero-depth expansion; it does not assume an old/future successful render or continuation.

The companion callback draft structurally keeps the full old finite callback contract, changes only the proof IH to CompleteWithHistory and appends the updated resource admission and false-restart histories. It calls callback_complete once and the stronger IH once only in the false branch at the actual returned frame. It chooses callbackFuel+resumeFuel before all extra/output quantifiers. Its runtime equality and returned history use the same explicit common-bound arithmetic. True callback rejection produces the old empty output list; no semantic truth is inferred from rejection. The callback draft is pending Root's serial strict check at preparation time.

This is an induction contract, a checked zero case and a submitted concrete callback step. It is not a positive-depth finite-history theorem. Head/sibling/ordinary/selected and parked producers must still construct these full certificates from original inputs. Seed/reservation provenance must come from their existing original schedules, not later Fits. Full native Caller/Memos and captured-cache witnesses cannot be replaced by query equality. No Satisfies statement or desired future action/history is an initial admission premise. No repository writes, builds, Git/network or prior frozen bundle edits were performed by this task. Do not freeze this bundle until both actual final sources and strict receipts are available.
''')
print(json.dumps({'input_sources':len(index),'input_cuts':sum(len(x['cuts']) for x in index),'contract_checked_sha256':sha(checked.encode()),'callback_pending_sha256':sha((base/'SourcePruningEnumerationFiniteCallbackHistory.lean').read_bytes()),'root_delta_spans':len(ops),'preparation_report_sha256':sha((base/'preparation-report.txt').read_bytes())},indent=2))
