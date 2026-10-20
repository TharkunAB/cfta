from pathlib import Path
h=Path(__file__).resolve().parent
old=Path('/tmp/mcfta-native-captured-stored-unfold-fixture/unfold-kernels.lean').read_text()
s=old.split('private def unfoldedRun',1)[0]
s=s.replace('SourceCurrentNativeCapturedMuUnfoldRows','SourceCurrentNativeOriginalCapturedMuRows').replace('CapturedStoredUnfoldFixture','OriginalCapturedMuFixture')
s=s.replace('# Actual captured Mu rows retain one source callback across unfolds','# An initial shared Mu retains its original source callback')
a=s.index('Two closed source binders');b=s.index('-/',a)
s=s[:a]+'''Two distinct outer binders share the same closed used inner Mu.
The actual outer optional captures that initial Mu at leaf occurrence one.
Its actual unfold row retains one original source publication and callback.
'''+s[b:]
s=s.replace('recursive "outerLeft" "innerLeft",recursive "outerRight" "innerRight"','recursive "outerLeft" "sharedInner",recursive "outerRight" "sharedInner"')
s=s.replace('private theorem new_capture : heap.nodeRecords entry.key = none ∧','private theorem initial_capture : heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧')
s=s.replace('heap.nodes.next = 17','heap.nodes.next = 13').replace('2^(17+17*17)','2^(13+13*13)')
# The resource exponent remains symbolic. Only its checked initial node count changes.
s+='''private def unfoldedRun := InternedFreshOrdinaryStoredSubstitution.unfold
  (.mu entry stored depth ordinary) current.native.machine.heap
private def unfolded : Node := match unfoldedRun with | .done value _ => value | .pending .. => .empty
private def unfoldedHeap : Heap := unfoldedRun.state
private def fallback : EdgeValue Symbol Guard := (run (makeEdge ("missing",.top) top []) (empty : Heap)).1
private def recRow (row : EdgeValue Symbol Guard) : Bool := row.entry.key.symbol == ("rec",.top)
private def unfoldedIndex : Nat := (InternedEdgeResidency.nodeEdges unfolded).findIdx recRow
private def storedIndex : Nat := (InternedEdgeResidency.nodeEdges stored).findIdx recRow
private def unfoldedRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]?.getD fallback
private def storedRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges stored)[storedIndex]?.getD fallback
private theorem actual_unfold : unfoldedRun = .done unfolded unfoldedHeap := by cbv
private theorem unfolded_selected : (InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]? = some unfoldedRow := by cbv
private theorem unfolded_fields : unfoldedRow.entry.key.symbol = ("rec",.top) ∧
    unfoldedRow.entry.key.constraint = top ∧ unfoldedRow.children = [.mu entry stored depth ordinary] := by
  constructor
  · cbv
  constructor <;> cbv
private theorem node_row {value : Node} {row : EdgeValue Symbol Guard}
    (selected : row ∈ InternedEdgeResidency.nodeEdges value) : Row value row := by
  cases value with
  | node => exact .node selected
  | empty | reference | union | mu => cases selected
private theorem stored_children : storedRow.children = [.reference (.interned entry.identity)] := by cbv
private theorem rows_distinct : unfoldedRow ≠ storedRow := by
  intro same
  have different : (unfoldedRow.children.map Value.referenceOf == storedRow.children.map Value.referenceOf) = false := by cbv
  rw [same] at different
  simp only [beq_self_eq_true] at different
  cases different
private theorem stored_rec_unique (row : EdgeValue Symbol Guard) (inside : RowAt stored row)
    (symbol : row.entry.key.symbol = ("rec",.top)) : row = storedRow := by
  have shape : (match stored with | .node .. => True | _ => False) := by cbv
  have filtered : (InternedEdgeResidency.nodeEdges stored).filter recRow = [storedRow] := by cbv
  cases actual : stored with
  | node selected rows level free =>
      rw [actual] at inside filtered
      change rows.filter recRow = [storedRow] at filtered
      cases inside with
      | node found =>
          have member : row ∈ rows.filter recRow := List.mem_filter.mpr
            ⟨List.mem_of_getElem? found,by simp only [recRow,symbol,beq_self_eq_true]⟩
          rw [filtered] at member
          exact List.mem_singleton.mp member
  | empty | reference | union | mu => simp only [actual] at shape

end MicroCFTA.OriginalCapturedMuFixture
'''
(h/'original-kernels.lean').write_text(s)
for a,b in [('unfold-kernels-run-check.py','original-kernels-run-check.py'),('unfold-kernels-capped-worker.py','original-kernels-capped-worker.py')]:
 text=(Path('/tmp/mcfta-native-captured-stored-unfold-fixture')/a).read_text().replace('unfold-kernels','original-kernels').replace('UNFOLD_KERNELS','ORIGINAL_KERNELS')
 (h/b).write_text(text)
