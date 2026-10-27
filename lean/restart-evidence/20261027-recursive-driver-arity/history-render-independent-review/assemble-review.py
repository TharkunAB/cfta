from pathlib import Path
import hashlib,json,re,difflib
root=Path('/tmp/mcfta-recursive-driver-arity-20261027')
repo=Path('/home/tritlo/Code/mcfta')
out=root/'history-render-independent-review'
def sha(b): return hashlib.sha256(b).hexdigest()
def save(path,b):
 p=out/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return p
records=[]
def take(src,dst,cuts=(),scope='Whole source read'):
 p=Path(src);b=p.read_bytes(); save(dst,b)
 rec={'source_path':str(p),'copy':dst,'bytes':len(b),'sha256':sha(b),'lines':len(b.splitlines()),'review_scope':scope,'cuts':[]}
 for a,z,label in cuts:
  cut=b''.join(b.splitlines(keepends=True)[a-1:z]); rel=f'cuts/{Path(dst).stem}-{label}-{a}-{z}.lean'
  save(rel,cut);rec['cuts'].append({'path':rel,'start_line':a,'end_line':z,'bytes':len(cut),'sha256':sha(cut)})
 records.append(rec);return b.decode()
post=take(root/'history-output-keeps/drafts/v3/SourcePruningEnumerationHistoryPost.lean','sources/SourcePruningEnumerationHistoryPost.lean',[(25,49,'actual-post')])
arity=take(root/'history-output-arity/drafts/v1/SourcePruningEnumerationHistoryOutputArity.lean','sources/SourcePruningEnumerationHistoryOutputArity.lean',[(37,65,'backward-edges')])
joint=take(root/'history-output-arity/drafts/v1/SourcePruningEnumerationFiniteHistoryResourcesArity.lean','sources/SourcePruningEnumerationFiniteHistoryResourcesArity.lean',[(30,64,'contract'),(65,97,'common-bound')])
render=take(root/'render-consumer/drafts/v3/SourcePruningEnumerationFiniteHistoryRenderingArity.lean','sources/SourcePruningEnumerationFiniteHistoryRenderingArity.lean',[(32,88,'render-contract'),(89,101,'actual-consumer')])
oldjoint=take(repo/'lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryResources.lean','old/SourcePruningEnumerationFiniteHistoryResources.lean',[(50,78,'old-full-header')])
oldrender=take(repo/'lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryRendering.lean','old/SourcePruningEnumerationFiniteHistoryRendering.lean',[(31,89,'old-full-header')])
support=[
 ('SourcePruningEnumerationFiniteHistoryContract.lean',[(45,140,'actual-history')],'Whole initial section through line 220 read; later code copied for provenance'),
 ('SourcePruningEnumerationOrdinaryReceiptArity.lean',[(27,67,'resident-from-scan')],'Whole source read'),
 ('SourcePruningEnumerationResourceHistoryMeaning.lean',[(31,120,'annotated-history'),(164,185,'meaning-inputs')],'Definitions and theorem headers through line 190 read; later proof retained as provenance'),
 ('SourcePruningEnumerationHistoryRenderingSoundness.lean',[(39,101,'actual-render-soundness')],'Whole source read'),
 ('SourcePruningEnumerationArityOrigins.lean',[(24,44,'key-dependent-heap')],'Initial definitions and operations through line 115 read; remaining construction proofs retained as provenance'),
 ('SourceCurrentAllocatedPartialInvariant.lean',[(27,46,'context-post'),(66,79,'post-composition')],'Whole source read'),
 ('SourceEqualityRequiredCache.lean',[(24,43,'keeps')],'Whole source read'),
 ('InternedConstructorTemplates.lean',[(73,89,'literal-record-growth')],'Only the listed literal cut read; whole file copied for provenance'),
 ('SourcePruningEnumerationResourceHistoryCanonical.lean',[(36,84,'canonical-output')],'Whole source read')]
for name,cuts,scope in support: take(repo/'lean/MicroCFTA'/name,'support/'+name,cuts,scope)
take(root/'history-output-arity/inputs/SourcePruningEnumerationFiniteArityContract.lean','support/SourcePruningEnumerationFiniteArityContract.lean',[(32,67,'aggregate-own-output-heap')],'Definition and forgetting proof lines 25-110 read; remaining zero-case code retained as provenance')
take(root/'driver-step/drafts/v1/SourcePruningEnumerationFiniteResourcesArity.lean','support/SourcePruningEnumerationFiniteResourcesArity.lean',[(29,77,'depth-producer')],'Whole source read; positive dependencies reviewed in separate OPEN driver-step-independent-review')
# Keep failed source revisions and final-only repairs unchanged.
for version in ('v1','v2'):
 take(root/'render-consumer/drafts'/version/'SourcePruningEnumerationFiniteHistoryRenderingArity.lean',f'revisions/render-{version}.lean',scope='Whole revision compared with final; header-only changes recorded')
checks=[]
for check,module,expect in [
 ('strict-history-post-1','SourcePruningEnumerationHistoryPost',False),
 ('strict-history-post-2','SourcePruningEnumerationHistoryPost',True),
 ('strict-historyoutputarity-1','SourcePruningEnumerationHistoryOutputArity',True),
 ('strict-finitehistoryresourcesarity-1','SourcePruningEnumerationFiniteHistoryResourcesArity',True),
 ('strict-finitehistoryrenderingarity-1','SourcePruningEnumerationFiniteHistoryRenderingArity',False),
 ('strict-finitehistoryrenderingarity-2','SourcePruningEnumerationFiniteHistoryRenderingArity',False),
 ('strict-finitehistoryrenderingarity-3','SourcePruningEnumerationFiniteHistoryRenderingArity',True)]:
 rp=root/check/'report.json'; rb=rp.read_bytes(); report=json.loads(rb)
 raw=(root/check/'raw.log').read_bytes(); snapshot=(root/check/'MicroCFTA'/f'{module}.lean').read_bytes()
 assert report['source_sha256']==sha(snapshot)
 assert report['bytes']==len(raw) and report['sha256']==sha(raw)
 assert (report['exit_code']==0)==expect
 assert report['cgroup_limits']['memory.max']=='4294967296' and report['cgroup_limits']['memory.swap.max']=='0'
 if expect: assert len(raw)==0
 for src,dst in [(rp,'report.json'),(root/check/'raw.log','raw.log'),(root/check/'MicroCFTA'/f'{module}.lean',f'{module}.lean')]:
  b=Path(src).read_bytes();save(f'evidence/{check}/{dst}',b)
  records.append({'source_path':str(src),'copy':f'evidence/{check}/{dst}','bytes':len(b),'sha256':sha(b),'review_scope':'Actual Root check receipt/source; no compiler run by this reviewer'})
 checks.append({'check':check,'module':module,'source_sha256':sha(snapshot),'exit_code':report['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'memory_max':report['cgroup_limits']['memory.max'],'swap_max':report['cgroup_limits']['memory.swap.max'],'scope':report.get('status')})
 if expect: assert snapshot==save.__globals__['out'].joinpath('sources',f'{module}.lean').read_bytes()
# Installed source is a separate observed identity, not inferred from TEMP compilation.
installed=[]
for name in ('HistoryPost','HistoryOutputArity','FiniteHistoryResourcesArity','FiniteHistoryRenderingArity'):
 module='SourcePruningEnumeration'+name;p=repo/'lean/MicroCFTA'/f'{module}.lean';b=p.read_bytes()
 assert b==(out/'sources'/p.name).read_bytes()
 installed.append({'source_path':str(p),'bytes':len(b),'sha256':sha(b),'matches_reviewed_final':True})
save('installed-validation.json',(json.dumps(installed,indent=2)+'\n').encode())
for rel in ('installed-history-arity.json','build-history-rendering-arity-1/report.json','build-history-rendering-arity-1/raw.log','render-consumer/contract-comparison-v3.json'):
 b=(root/rel).read_bytes();dst='evidence/root-'+rel.replace('/','--');save(dst,b);records.append({'source_path':str(root/rel),'copy':dst,'bytes':len(b),'sha256':sha(b),'review_scope':'Actual Root installation/build or supplied recovery evidence; independently validated where described'})
build=json.loads((root/'build-history-rendering-arity-1/report.json').read_text()); raw=(root/'build-history-rendering-arity-1/raw.log').read_bytes()
assert build['exit_code']==0 and build['bytes']==len(raw) and build['sha256']==sha(raw)
assert build['cgroup_limits']['memory.max']=='4294967296' and build['cgroup_limits']['memory.swap.max']=='0'
# Independent full declaration recovery. This parser skips internal named-argument := tokens.
def header(text,name):
 start=text.index('theorem '+name+'\n'); body=text[start:]; end=re.search(r' :=(?: by)?\n',body)
 assert end;return body[:end.start()]
oldj=header(oldjoint,'run_finite_complete_resources_with_history')
newj=header(joint,'run_finite_complete_resources_with_history_arity')
recoveredj=newj.replace('theorem run_finite_complete_resources_with_history_arity','theorem run_finite_complete_resources_with_history',1)
recoveredj=recoveredj.replace('\n    (arity : ArityHeap caller.checked.native.machine.heap)','',1)
recoveredj=recoveredj[:recoveredj.index(') ∧\n      OutcomeResourcesWithArity')]
recoveredj=recoveredj.replace('      (∀ extra output,','      ∀ extra output,',1)
assert recoveredj==oldj
oldr=header(oldrender,'run_finite_complete_resources_render_sound')
newr=header(render,'run_finite_complete_resources_render_sound_from_initial_arity')
removed='        ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver\n          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling\n          (SourcePruningEnumerationRestart.decision stop order metadata before) output →\n'
recoveredr=newr.replace('theorem run_finite_complete_resources_render_sound_from_initial_arity','theorem run_finite_complete_resources_render_sound',1)
recoveredr=recoveredr.replace('\n    (arity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap)','',1)
recoveredr=recoveredr.replace('∀ (_extra : Nat) output,','∀ extra output,',1)
needle='      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →\n'
assert recoveredr.count(needle)==1
recoveredr=recoveredr.replace(needle,needle+removed,1)
assert recoveredr==oldr
supplied=json.loads((root/'render-consumer/contract-comparison-v3.json').read_text());assert supplied['old']==oldr and supplied['new']==newr and supplied['recovered']==oldr
recoveries=[]
for name,old,new,recovered,mapping in [
 ('joint-finite-history',oldj,newj,recoveredj,'Rename theorem; remove only last initial arity binder and appended OutcomeResourcesWithArity/ResourceHistoryWithArity outputs; remove grouping parentheses needed to append.'),
 ('final-render',oldr,newr,recoveredr,'Rename theorem; remove only last initial arity binder; restore old supplied ResourceHistoryWithArity observer antecedent; undo retained _extra : Nat binder annotation.')]:
 for tag,text in [('old',old),('new',new),('recovered',recovered)]:save(f'contracts/{name}-{tag}.lean.txt',text.encode())
 recoveries.append({'contract':name,'old_bytes':len(old.encode()),'old_sha256':sha(old.encode()),'new_bytes':len(new.encode()),'new_sha256':sha(new.encode()),'recovered_sha256':sha(recovered.encode()),'byte_exact':old==recovered,'mapping':mapping})
save('old-contract-recovery.json',(json.dumps(recoveries,indent=2)+'\n').encode())
deltas=[]
versions=[(out/'revisions/render-v1.lean').read_text(),(out/'revisions/render-v2.lean').read_text(),render]
for i in range(2):
 diff=''.join(difflib.unified_diff(versions[i].splitlines(True),versions[i+1].splitlines(True),fromfile=f'v{i+1}',tofile=f'v{i+2}'))
 save(f'revisions/render-v{i+1}-to-v{i+2}.diff',diff.encode());deltas.append({'from':f'v{i+1}','to':f'v{i+2}','diff':diff})
save('revision-validation.json',(json.dumps(deltas,indent=2)+'\n').encode())
save('check-validation.json',(json.dumps({'strict':checks,'installed_build':{'exit_code':build['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw)},'reviewer_ran_compiler':False},indent=2)+'\n').encode())
save('source-pins-initial.json',(json.dumps({'sources':records},indent=2)+'\n').encode())
print(json.dumps({'sources_evidence_records':len(records),'literal_cuts':sum(len(r.get('cuts',[])) for r in records),'files_before_report':len([p for p in out.rglob('*') if p.is_file()]),'recoveries':recoveries,'final_sources':installed},indent=2))
