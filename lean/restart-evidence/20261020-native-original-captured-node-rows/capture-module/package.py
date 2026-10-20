from pathlib import Path
import hashlib,json,shutil
p=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
def write(name,value):(p/name).write_text(json.dumps(value,indent=2)+'\n')
def pin(base,name):
 data=(base/name).read_bytes();return {'path':name,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
shutil.copyfile(p/'captured-node-rows-peaks.txt',p/'captured-node-rows-peaks-final.txt')
head='MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows'
write('captured-node-rows-selection.json',{'source':'SourceCurrentNativeOriginalCapturedNodeRows.lean',
 'sha256':pin(p,'SourceCurrentNativeOriginalCapturedNodeRows.lean')['sha256'],
 'selected_strict':'captured-node-rows-direct-2','selected_public':'captured-node-rows-public-1',
 'public_heads':[head],'lean_jobs':3,'failed_attempts':1,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,
 'unselected':[{'stem':'captured-node-rows-direct-1','status':'failed','reason':'Template substring replacement renamed the rows binder but not its uses; source Outcome.state also needed qualification. Exact word replacement and explicit InternedNestedConstruction.Outcome.state fixed elaboration without changing the intended contract.'}],
 'scope':'Actual native capture split; initial full cell has fixed indexed original node origins for stored and actual unfolded anchors. Generated branch unchanged. No global native rank or changed-child equality.'})
(p/'captured-node-rows-review.md').write_text('''# Original node calls for an actual initial Mu capture

The sole public producer is capture_node_rows. Its inputs match the actual capture_source interface: a completed original-empty build returns exactly the native entry heap, initial Good and native memo History, an actual checked node-request Trace to an optional site, current site-body availability, and an exact indexed full Mu occurrence in leaves. The leaves index is not identified with encode.slot.

The main proof derives entry SemanticHeap and causal MuPublication.History from the actual original source build. It calls the lower CapturedMuUnfoldRows.capture once. The later-generated branch's entire type is copied byte for byte from that lower producer. The proof returns the same generated tuple directly. It does not assign its generated encoded root to the original program.

The exact initial full-cell arm calls build_node_row_origins once. Its final-cell selector fixes one path, outer index, event, original Reached, exact key and full candidate, missing fact, prefix and three callback paths, and suffix to the entry heap before any rows or unfolds. Full candidate injectivity explicitly retains entry, body, depth, and ordinary alignment. The same path's sites and final-cell selector remain in the result. The generic stored-row clause uses that same outer lookup and full body alignment to derive each original node SourceRow and full RowCall.

The private captured_unfold_nodes snippet was authored and checked separately by guard_inventory and is copied byte for byte. It derives current SemanticHeap and causal publication History from the same actual source build and checked Trace via source_trace. It derives the captured full Mu's availability from the actual leaves lookup and site-body availability. No current or future physical history is a caller premise. Native memo History is not used as physical publication history.

For each actual successful unfold at this same current heap, unfold_rows derives semantic, physical growth, issued extension, output availability, and extended causal history. Each actual literal returned row retains an original storedRow, its body RowAt, exact symbol and guard, equal arity, and identity or actual ordered Calls from stored children to returned children. The same fixed path and outer lookup then supply ultimate original node production for that storedRow. The full source RowCall equals storedRow. It is not equated with a returned row whose children changed.

Every node result retains producer index at most the fixed outer index, the same path lookup, generic SyntaxBound and UnionDescent relative to that producer expression, rich Context, original Reached, SourceRow, actual node build, buildEdges and makeNode, distinct source and canonical output indices, full RowCall, and forward physical and issued suffixes to outer.afterBody. No old Observed or Stored event is selected and identified with this indexed event.

Selected strict2 has a zero-byte log. The complete FULL1 printer contains the public type and proof with all eight settings. Its axioms are limited to propext, Classical.choice, and Quot.sound. The expanded public type has no private helper identifier. Three own capped jobs are retained: one failed statement-template/Outcome elaboration draft, one successful strict check, and one successful full printer. All use pinned Lean 4.34.1, all linters, effective 4 GiB memory.max/high, zero swap, the five-minute wrapper, and fresh usage. This component adds one public group, no constructed group, and no canonical job.

The result adds no future completion, supplied row-preservation law, unique writer occurrence, current-callback identity, or original-program claim for the later-generated branch. It does not identify the actual changed children with original stored children. It does not carry an arbitrary residual reader continuation, establish global native renewal or termination, or prove Haskell refinement. The source build must end at the exact native entry heap.

Run captured-node-rows-verify.py from any directory. Ordinary verification uses retained ROOT snapshots. --live also compares a live ROOT selected with --root. The verifier invokes no Lean process. The manifest excludes itself, generated verification output, mutable peaks, and other owners' mutable files. All own proof attempts are retained.
''')
modules=['SourceCurrentNativeOriginalNodeRowOrigins','SourceCurrentNativeCapturedMuUnfoldRows',
 'SourceCurrentNativePublicationTrace','SourceCurrentNativeMuPublication','SourceRecursiveIntersectionSemanticHeap',
 'InternedStoredSubstitution','SourceCurrentAllocatedNativePhysicalTraceCompletion',
 'SourceCurrentAllocatedNativePhysicalCompletion','SourceCurrentNativeEdgeWriterGrowth',
 'SourceCurrentNativeCapturedMuStoredRows','SourceCurrentBuildStructuralRowOrigins','SourceCurrentNativeMuWriterSourceRows']
sources=[]
for module in modules:
 name='lean/MicroCFTA/'+module+'.lean';sources.append(pin(root,name))
 target=p/'inputs'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/name,target)
write('captured-node-rows-source-pins.json',{'snapshot_root':'inputs','files':sources})
files=['SourceCurrentNativeOriginalCapturedNodeRows.lean','captured-node-rows-run-check.py','captured-node-rows-capped-worker.py',
 'captured-node-rows-public.lean','assemble.py','header.lean.txt','captured-unfold-node-snippet.lean.txt',
 'generated-branch.lean.txt','node-origin-result.lean.txt','public-producer.lean.txt','captured-node-rows-selection.json',
 'captured-node-rows-review.md','captured-node-rows-source-pins.json','captured-node-rows-verify.py','captured-node-rows-peaks-final.txt']
for stem in ['captured-node-rows-direct-1','captured-node-rows-direct-2','captured-node-rows-public-1']:
 files += [stem+suffix for suffix in ['.json','.source.lean','.log','.limits.json','.usage.json']]
write('captured-node-rows-manifest.json',{'schema':1,'files':[pin(p,n) for n in files],'sources':sources,
 'public_heads':[head],'lean_jobs':3,'failed_attempts':1,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0})
