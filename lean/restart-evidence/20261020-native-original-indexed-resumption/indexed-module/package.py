from pathlib import Path
import hashlib,json,shutil
p=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
def write(name,value):
 (p/name).write_text(json.dumps(value,indent=2)+'\n')
def pin(base,name):
 data=(base/name).read_bytes();return {'path':name,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
# The saved assembly recipe uses only retained task-owned inputs.
a=(p/'assemble.py').read_text().replace("Path('/tmp/mcfta-native-indexed-binder-before/binder-before-snippet.lean.txt')","(p/'binder-before-snippet.lean.txt')")
(p/'assemble.py').write_text(a)
shutil.copyfile(p/'indexed-resumption-peaks.txt',p/'indexed-resumption-peaks-final.txt')
heads=['MicroCFTA.SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions']
write('indexed-resumption-selection.json',{
 'source':'SourceCurrentNativeOriginalIndexedResumption.lean','sha256':pin(p,'SourceCurrentNativeOriginalIndexedResumption.lean')['sha256'],
 'selected_strict':'indexed-resumption-direct-1','selected_public':'indexed-resumption-public-1',
 'public_heads':heads,'lean_jobs':2,'failed_attempts':0,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,
 'scope':'One completed original-empty source build fixes one publication path and indexed row resumptions. No global native rank or runtime correspondence claim.'})
(p/'indexed-resumption-review.md').write_text('''# Indexed original-source row resumptions

The sole public producer is `build_row_resumptions`. Its only caller premise is the actual completed `build original [] empty` equation. Its native symbol and guard instances match the existing source consumers.

The producer calls `build_trace_writers` once. The returned path stays fixed for all indexed sites, final-cell selections, precompletion selections, and stored-row resumptions. The first three trace clauses are retained unchanged. Each indexed outer event fixes one raw callback, actual build, actual self filter, historical Context, and original-source Reached before its all-row clause.

The private joint SourceRow induction is copied from the frozen UnionDescent module. It retains the same terminal expression, inputs, entry heap, raw value, and return heap. It derives the union-only route with those witnesses. Actual union prefix, selected member call, suffix, and makeUnion receipts supply forward physical and issued growth. The empty original input path excludes row-bearing captures. The generic SyntaxBound is reused with its original instance. No Context is inferred from arbitrary Reached.

The node arm retains the actual ordered RowCall, source index, canonical output index, buildEdges result, and makeNode result. It does not require a child. Nullary rows remain covered.

The binder core is the exact frozen private snippet authored and checked separately by guard_inventory. The integration retains the current terminal depth probe, ordinary probe, request, exact selected full payload at terminalAfter, smart finish, and structural stored-row anchor. Actual suffix growth reaches rawAfter. The actual self filter then supplies growth and issued extension to the enclosing event's afterBody, before its completion. The selected full record is forwarded to that heap. The common path's precompletion selector yields an earlier index strictly smaller than the outer index, the same indexed event, original Reached, exact key and full candidate, missing fact, prefix and three callback paths, and suffix to outer.afterBody.

The integration unpacks that earlier event once. Its actual callback is fixed before all stored rows. Full Mu payload injectivity aligns its body with the selected stored body. The selected row and all stored rows obtain raw RowAt and SourceRow receipts at that same earlier callback. No Stored or Observed conversion reselects a writer. No current callback is identified with a historical warm winner.

The public expanded type contains no private helper identifiers. The selected strict log has zero bytes. The full public check prints the complete type and proof with all eight settings and checks its axioms. The allowed axiom set is propext, Classical.choice, and Quot.sound. Both attempts passed. Each used effective memory.max and memory.high of 4 GiB, zero swap, a five-minute wrapper, the pinned Lean 4.34.1 toolchain, and fresh usage above the stop threshold. This package runs no canonical build and adds no constructed example.

The result concerns structural RowAt of stored bodies. It does not add the universal actual-unfold interface. Publication index decreases only within this one completed original source trace. The result does not prove a global future native rank, generated-root ancestry, unique source occurrence, unique writer syntax, runtime termination, or Haskell refinement. Source child descent, residual Mu observations, generated roots with nonempty capture pools, and global renewal remain separate obligations.

Run indexed-resumption-verify.py from any directory. Ordinary verification uses retained ROOT snapshots. --live also compares the live ROOT files; --root selects a relocated ROOT. The verifier invokes no Lean process. The manifest excludes itself, the generated verification result, and the mutable peaks file. Every proof attempt is retained.
''')
modules=['SourceCurrentNativeOriginalPublicationTrace','SourceCurrentNativeOriginalUnionDescent',
 'SourceCurrentNativeOriginalObservedResume','SourceCurrentPublicationBodySourceRows',
 'SourceCurrentNativeMuPublication','SourceCurrentNativeMuPublicationCallbacks','SourceCurrentNativeMuIssuedHistory',
 'SourceCurrentCompletedBuildRootedWriters','SourceCurrentSourceCaptureOriginalSlots',
 'SourceCurrentBuildStructuralRowOrigins','SourceCurrentConstrainedCapSourceHistory','InternedFreshOrdinaryFacts',
 'InternedFreshOrdinarySourceHistory','InternedFreshOrdinaryActiveOrigins','InternedProbeProvenance']
sources=[]
for module in modules:
 name='lean/MicroCFTA/'+module+'.lean'
 entry=pin(root,name);sources.append(entry)
 target=p/'inputs'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/name,target)
write('indexed-resumption-source-pins.json',{'snapshot_root':'inputs','files':sources})
files=['SourceCurrentNativeOriginalIndexedResumption.lean','indexed-resumption-run-check.py',
 'indexed-resumption-capped-worker.py','indexed-resumption-public.lean','joint-helpers.lean.txt',
 'binder-before-snippet.lean.txt','callback-rows.lean.txt','header.lean.txt','public-producer.lean.txt',
 'assemble.py','indexed-resumption-selection.json','indexed-resumption-review.md',
 'indexed-resumption-source-pins.json','indexed-resumption-verify.py','indexed-resumption-peaks-final.txt']
for stem in ['indexed-resumption-direct-1','indexed-resumption-public-1']:
 files += [stem+suffix for suffix in ['.json','.source.lean','.log','.limits.json','.usage.json']]
write('indexed-resumption-manifest.json',{'schema':1,'files':[pin(p,n) for n in files],'sources':sources,
 'public_heads':heads,'lean_jobs':2,'failed_attempts':0,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0})
