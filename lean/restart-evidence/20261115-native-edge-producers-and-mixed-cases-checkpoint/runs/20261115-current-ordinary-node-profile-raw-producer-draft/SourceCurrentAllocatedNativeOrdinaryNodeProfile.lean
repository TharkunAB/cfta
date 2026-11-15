import MicroCFTA.SourceCurrentAllocatedNativeRowsPhysicalReadback
import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
import MicroCFTA.SourceCurrentAllocatedNativeRequestResults

/-!
# Ordinary native node result profiles

Actual ordered edge queries supply profiles for their returned children.
The canonical node constructor retains closedness and only the source atom.
The proof keeps the original node prefix, budgets and full endpoints.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOrdinaryNodeProfile
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceRecursiveIntersectionControl (decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid

set_option autoImplicit false

private theorem ordinary_payload (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    SourceRecursiveIntersectionControl.payload request.left request.right = .ordinary := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact selected

private theorem ordinary_code [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    compileNode request = compileRows request.domain (InternedEdgeResidency.nodeEdges request.left) (InternedEdgeResidency.nodeEdges request.right) := by
  have payload := ordinary_payload request selected
  cases left : request.left <;> cases right : request.right <;>
    simp only [left,right,SourceRecursiveIntersectionControl.payload] at payload <;> try cases payload
  unfold compileNode
  simp only [selected]
  rw [left,right]
  rfl

private theorem make_node_profile [DecidableEq (EdgeKey Symbol Guard)]
    (sourceName : Nat) (rows : List (EdgeValue Symbol Guard))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (resident : ∀ row ∈ rows, EdgeResident heap row)
    (profiles : ∀ row ∈ rows, ∀ child ∈ row.children, Profile sourceName child) :
    Profile sourceName (run (makeNode rows) heap).1 := by
  refine ⟨?_, ?_⟩
  · rw [InternedNormalizationFree.makeNode_free rows heap facts.coherent facts.linked resident]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    obtain ⟨child, included, named⟩ :=
      (childFree_member ((canonicalEdges (surviving rows)).flatMap EdgeValue.children) name).mp member
    obtain ⟨row, selected, inRow⟩ := List.mem_flatMap.mp included
    have rawMember : row ∈ rows :=
      (List.mem_filter.mp (canonicalEdges_member (surviving rows) row selected)).1
    rw [(profiles row rawMember child inRow).1] at named
    cases named
  · intro atom occurrence
    have raw := InternedBoundaryAtoms.makeNode_atom_origin rows heap facts.coherent facts.linked resident atom occurrence
    obtain ⟨row, included, child, inRow, selected⟩ := (InternedBoundaryAtoms.edge_member rows atom).mp raw
    exact (profiles row included child inRow).2 atom selected

/-- The actual ordinary node body derives its profile from genuine smaller ordered edge results. -/
theorem ordinary_node_profile_trace_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard) (sourceName : Nat)
    (request : NodeRequest Symbol Guard) (original before after : Checked width)
    (parentFuel bodySteps : Nat) (result : Value Symbol Guard)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (physical : Physical original.native) (sourceGrowth : Grows sourceHeap original.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid original.operations)
    (plan : InputsThrough parentFuel (.code (.node request .pure)) original)
    (fields : FieldsThrough parentFuel (.code (.node request .pure)) original)
    (entered : Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) before)
    (smaller : bodySteps < parentFuel)
    (actual : Steps bodySteps (.code (compileNode request)) before (.code (.pure result)) after)
    (edges : ∀ pair ∈ pairs (nodeEdges request.left) (nodeEdges request.right),
      ∀ (childNext : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (childBefore childAfter : Checked width) (used count : Nat) (childValue : EdgeValue Symbol Guard),
      0 < used → used + count ≤ parentFuel →
      Steps used (.code (.node request .pure)) original
        (.code ((requestEdge request.domain pair.1 pair.2).bind childNext)) childBefore →
      Steps count (.code (requestEdge request.domain pair.1 pair.2)) childBefore
        (.code (.pure childValue)) childAfter →
      ∀ child ∈ childValue.children, Profile sourceName child) :
    Profile sourceName result ∧
    Physical after.native ∧ Extension original.native.machine after.native.machine ∧
    Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    Available after.native.machine.heap result ∧
    ∃ (rows : List (EdgeValue Symbol Guard)) (middle : Checked width) (count : Nat),
      count + 1 ≤ bodySteps ∧
      All₂ (fun (_pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) row =>
        ∀ child ∈ row.children, Profile sourceName child)
        (pairs (nodeEdges request.left) (nodeEdges request.right)) rows ∧
      Physical middle.native ∧ Extension before.native.machine middle.native.machine ∧
      (∀ row ∈ rows, EdgeResident middle.native.machine.heap row) ∧
      Trace count (.code (compileRows request.domain (nodeEdges request.left) (nodeEdges request.right))) before
        (.code (.work (makeNode rows) .pure)) middle ∧
      result = (run (makeNode rows) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeNode rows) middle.native.machine.heap).2}} ∧
      nodeEdges result = canonicalEdges (surviving rows) := by
  have compiled := ordinary_code request selected
  have dispatched := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel 1 (.code (.node request .pure)) (.code (compileNode request)) finishNext
    original before sourceHeap physical plan fields operationsValid sourceGrowth entered (by omega)
  obtain ⟨_checkedEntry, firstPhysical, firstExtension, firstGrowth, firstOperationsValid,
    _firstOperationsGrowth, _boundPlan, rawPlan, _boundFields, rawFields⟩ := dispatched
  have completed := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    (parentFuel - 1) bodySteps (.code (compileNode request)) (.code (.pure result)) .pure
    before after sourceHeap firstPhysical rawPlan rawFields firstOperationsValid firstGrowth actual (by omega)
  obtain ⟨bodyTrace, afterPhysical, bodyExtension, afterGrowth, afterOperationsValid,
    _afterOperationsGrowth, _boundAfterPlan, _rawAfterPlan, _boundAfterFields, _rawAfterFields⟩ := completed
  have rowsTrace : Trace bodySteps
      (.code (compileRows request.domain (InternedEdgeResidency.nodeEdges request.left)
        (InternedEdgeResidency.nodeEdges request.right))) before (.code (.pure result)) after := by
    rw [← compiled]
    exact bodyTrace
  have rowsDone := trace_done bodySteps _ before after result rowsTrace.steps
  have observed := SourceCurrentAllocatedNativeRowsPhysicalReadback.compile_rows_physical_readback_of_smaller_edges
    request.domain (InternedEdgeResidency.nodeEdges request.left) (InternedEdgeResidency.nodeEdges request.right)
    before after (bodySteps + 1) bodySteps result
    (fun (_pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (row : EdgeValue Symbol Guard) =>
      ∀ child ∈ row.children, Profile sourceName child)
    firstPhysical rowsDone rowsTrace (by
      intro stepsBefore childFuel room _childSmaller pair member next first last row origin childPhysical childDone
      obtain ⟨rawCount, rawSmaller, rawSteps⟩ := done_trace childFuel _ first last row childDone
      let lifted : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
        fun value => (next value).bind finishNext
      have bodyPrefix : Steps stepsBefore (.code (compileNode request)) before
          (.code ((requestEdge request.domain pair.1 pair.2).bind next)) first := by
        rw [compiled]
        exact origin
      have appended := bodyPrefix.bind _ _ _ _ _ finishNext
      have outer : Steps (1 + stepsBefore) (.code (.node request .pure)) original
          (.code ((requestEdge request.domain pair.1 pair.2).bind lifted)) first := by
        simpa only [Control.bind, Code.bind_assoc, lifted] using
          entered.trans _ _ _ _ _ _ _ _ appended
      obtain ⟨_remaining, _total, _checkedPrefix, atQuery⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix origin rowsTrace
      obtain ⟨_rest, _length, boundQuery, _remainingTrace⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix
          (rawSteps.bind _ _ _ _ _ next) atQuery
      have rawChecked := SourceCurrentHereditaryNativePhysicalSplit.unbind rawSteps next boundQuery
      exact ⟨edges pair member lifted first last (1 + stepsBefore) rawCount row
          (by omega) (by omega) outer rawSteps,
        SourceCurrentAllocatedNativeRequestResults.edge_result rawCount
          ⟨request.domain, pair.1, pair.2⟩ first last row childPhysical rawChecked⟩)
  obtain ⟨rows, middle, count, countBound, _walked, aligned, middlePhysical,
    middleExtension, resident, throughWork, resultEq, afterEq, canonical, _resultFree,
    _rowsAfterPhysical, _rowsAfterExtension, available, _rowsAfterResident⟩ := observed
  have rowProfiles : ∀ row ∈ rows, ∀ child ∈ row.children, Profile sourceName child := by
    induction aligned with
    | nil =>
        intro row member
        cases member
    | cons head tail ih =>
        intro row member
        cases member with
        | head => exact head
        | tail _ included => exact ih row included
  have profile : Profile sourceName result := by
    rw [resultEq]
    exact make_node_profile sourceName rows middle.native.machine.heap middlePhysical.machine.1 resident rowProfiles
  exact ⟨profile, afterPhysical, firstExtension.trans bodyExtension, afterGrowth,
    afterOperationsValid, available, rows, middle, count, by omega, aligned, middlePhysical,
    middleExtension, resident, throughWork, resultEq, afterEq, canonical⟩

end MicroCFTA.SourceCurrentAllocatedNativeOrdinaryNodeProfile
