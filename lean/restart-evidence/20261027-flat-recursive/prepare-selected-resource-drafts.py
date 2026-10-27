from pathlib import Path
import re,hashlib,json
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');out=Path('/tmp/mcfta-flat-recursive-20261027/selected-resources-draft')
s=(repo/'SourceFlatPruningSelectedCompletion.lean').read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationSelectedEdge\n','import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources\n').replace('import MicroCFTA.SourceFlatPruningTraversalCompletion','import MicroCFTA.SourceFlatPruningTraversalResources')
s=s.replace('SourceFlatPruningSelectedCompletion','SourceFlatPruningSelectedResources').replace('(Result Ranges run finish finish_safe finish_protected)','(Result run finish finish_safe finish_protected cost)')
s=s.replace('open SourceCurrentAllocatedPartialInvariant (Context Post)','open SourceCurrentAllocatedPartialInvariant (Context Post)\nopen SourcePruningEnumerationIncomingReservation (Seed advance Reserved)\nopen SourceCurrentConstrainedCapGeneratedQueryResources (Fits)')
s=s.replace('local notation "Fragment" => Fragments.Fragment Symbol','local notation "Fragment" => Fragments.Fragment Symbol\nlocal notation "Heap" => SourceEqualityAnnotationHeap.Heap')
s=s.replace('variable {width : Nat}','variable {bits : Nat}').replace('Caller width','Caller (bits + 2)').replace('Result width','Result (bits + 2)')
s=s.replace('theorem complete_with_fragments\n','theorem complete_with_fragments_resources\n    (seed : Seed)\n')
s=s.replace('    (ranges : Ranges checkEmpty scs edge caller before memos.query) :','    (fits : Fits seed.2 caller.checked)\n    (reserved : Reserved bits seed (cost edge scs before.core.counter tries))\n    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :')
needle='      (∀ (flat : EnumerationFlatCached.Cached Symbol Constraint),'
resources='      Fits (advance seed (cost edge scs before.core.counter tries)).2 afterCaller.checked ∧\n      Heap (fun guard => guard ∈ (advance seed (cost edge scs before.core.counter tries)).1)\n        afterCaller.checked.native.machine.heap ∧\n'
assert s.count(needle)==1;s=s.replace(needle,resources+needle)
a=s.index('  have numeric :');b=s.index('  obtain ⟨r, n, p, h, k, fragments',a);s=s[:a]+s[b:]
s=s.replace('fragmentBounds, shape, childrenFlat⟩ :=','fragmentBounds, shape, returnedFits, returnedKnown, childrenFlat⟩ :=')
s=s.replace('SourceFlatPruningTraversalCompletion.complete_with_fragments formulas','SourceFlatPruningTraversalResources.complete_with_fragments_resources seed formulas').replace('initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine numeric','initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine fits reserved known')
s=s.replace('fragmentSeparate⟩, flatRunning⟩','fragmentSeparate⟩, returnedFits, returnedKnown, flatRunning⟩').replace('.inr ⟨fragments, outer, waiting, rfl⟩, flatRunning⟩','.inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown, flatRunning⟩')
s=s.replace('# Original selected-edge completion with direct-parent execution','# Actual flat selected edges from original resources').replace('/-- Original selected-edge admission retains the full earlier packet and actual flat execution. -/','/-- Original resources retain the full selected-edge packet and actual flat execution. -/')
assert 'ranges' not in s.lower();assert 'width' not in s
p=out/'SourceFlatPruningSelectedResources.lean';p.write_text(s)
# Check entire existing original resource theorem header is retained before appended flat family.
def header(t,name):a=t.index('theorem '+name);return t[a:t.index(' := by',a)]
def norm(t):return re.sub(r'\s+','',t)
old=header((repo/'SourcePruningEnumerationSelectedEdgeResources.lean').read_text(),'complete_with_fragments_resources');new=header(s,'complete_with_fragments_resources');assert norm(new).startswith(norm(old))
# Captured source follows the existing two-producer common-bound alignment proof.
s=(repo/'SourceFlatPruningCapturedCompletion.lean').read_text()
s=s.replace('import MicroCFTA.SourceFlatPruningSelectedCompletion','import MicroCFTA.SourceFlatPruningSelectedResources\nimport MicroCFTA.SourcePruningEnumerationCapturedEdgeResources')
s=s.replace('SourceFlatPruningCapturedCompletion','SourceFlatPruningCapturedResources')
s=s.replace('open SourceCurrentAllocatedPartialInvariant (Context Post)','open SourceCurrentAllocatedPartialInvariant (Context Post)\nopen SourcePruningEnumerationIncomingReservation (Seed advance Reserved)\nopen SourceCurrentConstrainedCapGeneratedQueryResources (Fits)')
s=s.replace('local notation "Fragment" => Fragments.Fragment Symbol','local notation "Fragment" => Fragments.Fragment Symbol\nlocal notation "Heap" => SourceEqualityAnnotationHeap.Heap')
# Preserve generic private result_correct. Specialize only the public resource theorem and its body.
a=s.index('/-- Keep every old captured receipt');pre=s[:a];pub=s[a:]
pub=pub.replace('theorem complete_with_history\n','theorem complete_with_history_resources\n    (seed : Seed)\n').replace('Caller width','Caller (bits + 2)').replace('Result width','Result (bits + 2)')
pub=pub.replace('    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query) :','    (fits : Fits seed.2 caller.checked)\n    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))\n    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :')
# Replace its public header by the EXACT old resource theorem header plus the existing flat family.
oldText=(repo/'SourcePruningEnumerationCapturedEdgeResources.lean').read_text();oldHead=header(oldText,'complete_with_history_resources');flatStart=pub.index('      (∀ (flat : FlatCached),');flatEnd=pub.index(' := by',flatStart);family=pub[flatStart:flatEnd]
body=pub[pub.index(' := by')+len(' := by'):]
head=oldHead+' ∧\n'+family
body=body.replace('SourcePruningEnumerationCapturedEdge.complete_with_history formulas','SourcePruningEnumerationCapturedEdge.complete_with_history_resources seed formulas').replace('realized selected paths counts flags pending allowed tries residual projected ranges','realized selected paths counts flags pending allowed tries residual projected fits reserved known')
body=body.replace('_selectedShape, selectedFlat⟩ :=','_selectedShape, _selectedFits, _selectedKnown, selectedFlat⟩ :=')
body=body.replace('SourceFlatPruningSelectedCompletion.complete_with_fragments formulas','SourceFlatPruningSelectedResources.complete_with_fragments_resources seed formulas').replace('paths counts flags bounded pending allowed tries residual projected ranges','paths counts flags bounded pending allowed tries residual projected fits reserved known')
body=body.replace('  obtain ⟨oldRun, oldRest⟩ := packet','  obtain ⟨oldRun, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,\n    afterFlags, origin, afterPending, protects, pendingHistory, shape, returnedFits, returnedKnown⟩ := packet')
body=body.replace('afterCaller, after, savedQueries, final, next, afterRoots, result, ⟨shiftedRun, oldRest⟩, ?_⟩\n  obtain ⟨_post, _querySame, _growth, afterPaths, storage, _afterRealized,\n    afterCounts, afterFlags, _origin, _pending, _protects, _history, shape⟩ := oldRest','afterCaller, after, savedQueries, final, next, afterRoots, result, shiftedRun, post, querySame,\n    growth, afterPaths, storage, afterRealized, afterCounts, afterFlags, origin, afterPending,\n    protects, pendingHistory, shape, returnedFits, returnedKnown, ?_⟩')
assert 'oldRest' not in body
s=pre.replace('variable {width : Nat}','variable {width bits : Nat}')+head+' := by'+body
s=s.replace('# Flat observations of the complete captured-edge producer','# Actual flat captured edges from original resources')
assert ' ranges' not in s
p=out/'SourceFlatPruningCapturedResources.lean';p.write_text(s)
assert norm(header(s,'complete_with_history_resources')).startswith(norm(oldHead))
for p in out.glob('*.lean'):print(p.name,len(p.read_bytes()),len(p.read_text().splitlines()),hashlib.sha256(p.read_bytes()).hexdigest())
