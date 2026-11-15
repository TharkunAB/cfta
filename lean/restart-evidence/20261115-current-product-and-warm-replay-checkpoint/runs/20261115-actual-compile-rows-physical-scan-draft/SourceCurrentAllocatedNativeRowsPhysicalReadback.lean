import MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback
import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit

/-!
# Actual ordered row scans and physical node construction

The scan uses every pair from the actual symbol hash join.
The smaller query hypotheses concern the same parent execution.
The physical trace supplies each query's extension at its actual state.
The returned rows remain resident at the literal node constructor.
This module does not prove source-U normalization of live cross rows.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRowsPhysicalReadback
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => EdgeValue Symbol Guard × EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

set_option autoImplicit false

private theorem walk_readback
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state final : Checked width) (fuel traceFuel : Nat) (result : Value Symbol Guard)
    (rowLaw : Pair → EdgeValue Symbol Guard → Prop)
    (actual : Trace traceFuel (.code (compileRows domain left right)) state (.code (.pure result)) final)
    (children : ∀ stepsBefore childFuel, stepsBefore + childFuel < fuel → childFuel < fuel →
      ∀ pair ∈ pairs left right,
      ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (first last : Checked width) (row : EdgeValue Symbol Guard),
      Steps stepsBefore (.code (compileRows domain left right)) state
        (.code ((requestEdge domain pair.1 pair.2).bind next)) first →
      Physical first.native →
      SourceEqualityNativeDemand.execute childFuel (.code (requestEdge domain pair.1 pair.2)) first = .done row last →
      rowLaw pair row ∧ EdgeResident last.native.machine.heap row)
    (jobs : List Pair) (before : Checked width) (rows : List (EdgeValue Symbol Guard))
    (after : Checked width) (count : Nat)
    (walked : SourceEqualityNativeDemandWalkExecution.Walk
      (fun pair : Pair => requestEdge domain pair.1 pair.2) jobs before rows after count)
    (stepsBefore : Nat) (next : List (EdgeValue Symbol Guard) → Code Symbol Guard (Value Symbol Guard))
    (origin : Steps stepsBefore (.code (compileRows domain left right)) state
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestEdge domain pair.1 pair.2) jobs).bind next)) before)
    (bounded : stepsBefore + count + 1 < fuel) (physical : Physical before.native)
    (included : ∀ pair ∈ jobs, pair ∈ pairs left right) :
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      (∀ row ∈ rows, EdgeResident after.native.machine.heap row) ∧ All₂ rowLaw jobs rows := by
  induction walked generalizing stepsBefore next with
  | nil current =>
      exact ⟨physical, Extension.refl _, (by intro row member; cases member), .nil⟩
  | cons pair rest before middle after row rows firstFuel restFuel called tail ih =>
      let childNext : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
        fun row => (SourceRecursiveIntersectionCode.walk
          (fun pair : Pair => requestEdge domain pair.1 pair.2) rest).bind
          (fun rows => next (row :: rows))
      have atChild : Steps stepsBefore (.code (compileRows domain left right)) state
          (.code ((requestEdge domain pair.1 pair.2).bind childNext)) before := by
        simpa only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, childNext] using origin
      have advanced := called.bind _ _ _ _ _ childNext
      obtain ⟨_extra, _length, _physicalPrefix, queryTail⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix atChild actual
      obtain ⟨_remaining, _count, queryBound, _physicalTail⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix advanced queryTail
      have queryPhysical := SourceCurrentHereditaryNativePhysicalSplit.unbind called childNext queryBound
      have queryChecked := SourceCurrentNativeEnterCommonOperand.checked_trace_extension queryPhysical physical
      have first := children stepsBefore (firstFuel + 1) (by omega) (by omega)
        pair (included pair List.mem_cons_self) childNext before middle row atChild physical
        (trace_done firstFuel _ before middle row called)
      have tailOrigin : Steps (stepsBefore + firstFuel) (.code (compileRows domain left right)) state
          (.code ((SourceRecursiveIntersectionCode.walk
            (fun pair : Pair => requestEdge domain pair.1 pair.2) rest).bind
            (fun rows => next (row :: rows)))) middle :=
        atChild.trans _ _ _ _ _ _ _ _ advanced
      have restIncluded : ∀ candidate ∈ rest, candidate ∈ pairs left right := by
        intro candidate member
        exact included candidate (List.mem_cons_of_mem _ member)
      have later := ih (stepsBefore + firstFuel) (fun rows => next (row :: rows))
        tailOrigin (by omega) queryChecked.1 restIncluded
      refine ⟨later.1, queryChecked.2.trans later.2.1, ?_, .cons first.1 later.2.2.2⟩
      intro selected member
      cases member with
      | head => exact edge_grows _ _ later.2.1.heap row first.2
      | tail _ member => exact later.2.2.1 selected member

private theorem node_fields
    [DecidableEq (EdgeKey Symbol Guard)] (rows : List (EdgeValue Symbol Guard))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts heap)
    (resident : ∀ row ∈ rows, EdgeResident heap row) :
    nodeEdges (run (makeNode rows) heap).1 = canonicalEdges (surviving rows) ∧
      (run (makeNode rows) heap).1.free =
        childFree ((canonicalEdges (surviving rows)).flatMap EdgeValue.children) := by
  have keptResident : ∀ row ∈ canonicalEdges (surviving rows), EdgeResident heap row := by
    intro row member
    exact resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  cases kept : canonicalEdges (surviving rows) with
  | nil =>
      simp [makeNode, kept, run, nodeEdges, Value.free, childFree, canonicalFree]
  | cons first rest =>
      obtain ⟨entry, same⟩ := identifyNode_readback (first :: rest) heap facts.coherent facts.linked
        (by simpa only [kept] using keptResident)
      simp only [makeNode, kept, run, same, identifyNode, nodeEdges, Value.free] <;> constructor <;> rfl

/-- Actual smaller edge queries derive ordered row readback, residency, and the exact node constructor endpoint. -/
theorem compile_rows_physical_readback_of_smaller_edges
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (before after : Checked width) (fuel traceFuel : Nat) (result : Value Symbol Guard)
    (rowLaw : Pair → EdgeValue Symbol Guard → Prop)
    (physical : Physical before.native)
    (done : SourceEqualityNativeDemand.execute fuel (.code (compileRows domain left right)) before = .done result after)
    (actual : Trace traceFuel (.code (compileRows domain left right)) before (.code (.pure result)) after)
    (children : ∀ stepsBefore childFuel, stepsBefore + childFuel < fuel → childFuel < fuel →
      ∀ pair ∈ pairs left right,
      ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (first last : Checked width) (row : EdgeValue Symbol Guard),
      Steps stepsBefore (.code (compileRows domain left right)) before
        (.code ((requestEdge domain pair.1 pair.2).bind next)) first →
      Physical first.native →
      SourceEqualityNativeDemand.execute childFuel (.code (requestEdge domain pair.1 pair.2)) first = .done row last →
      rowLaw pair row ∧ EdgeResident last.native.machine.heap row) :
    ∃ (rows : List (EdgeValue Symbol Guard)) (middle : Checked width) (count : Nat),
      count + 1 < fuel ∧
      SourceEqualityNativeDemandWalkExecution.Walk (fun pair : Pair => requestEdge domain pair.1 pair.2)
        (pairs left right) before rows middle count ∧
      All₂ rowLaw (pairs left right) rows ∧
      Physical middle.native ∧ Extension before.native.machine middle.native.machine ∧
      (∀ row ∈ rows, EdgeResident middle.native.machine.heap row) ∧
      Trace count (.code (compileRows domain left right)) before
        (.code (.work (makeNode rows) .pure)) middle ∧
      result = (run (makeNode rows) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeNode rows) middle.native.machine.heap).2}} ∧
      nodeEdges result = canonicalEdges (surviving rows) ∧
      result.free = childFree ((canonicalEdges (surviving rows)).flatMap EdgeValue.children) ∧
      Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧
      (∀ row ∈ rows, EdgeResident after.native.machine.heap row) := by
  obtain ⟨total, totalBound, completed⟩ := done_trace fuel _ before after result done
  let next : List (EdgeValue Symbol Guard) → Code Symbol Guard (Value Symbol Guard) :=
    fun rows => .work (makeNode rows) .pure
  obtain ⟨inner, outer, rows, middle, count, called, built⟩ := steps_bind_inverse total
    (.code (SourceRecursiveIntersectionCode.walk (fun pair : Pair => requestEdge domain pair.1 pair.2)
      (pairs left right))) next before after result completed
  have outerPositive : 0 < outer := by
    by_contra nonpositive
    have zero : outer = 0 := by omega
    subst outer
    cases (steps_zero _ _ _ _ built).1
  have bounded : inner + 1 < fuel := by omega
  have walked := SourceEqualityNativeDemandWalkExecution.trace_walk _ _ inner before middle rows called
  have origin : Steps 0 (.code (compileRows domain left right)) before
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestEdge domain pair.1 pair.2) (pairs left right)).bind next)) before :=
    .refl _ _
  have observed := walk_readback domain left right before after fuel traceFuel result rowLaw actual children
    (pairs left right) before rows middle inner walked 0 next origin (by omega) physical
    (by intro pair member; exact member)
  have throughWork : Steps inner (.code (compileRows domain left right)) before
      (.code (.work (makeNode rows) .pure)) middle := by
    simpa only [compileRows, Control.bind, next, Code.bind] using walked.trace.bind _ _ _ _ _ next
  obtain ⟨_extra, _traceLength, physicalPrefix, workTrace⟩ :=
    SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix throughWork actual
  have constructorChecked := SourceCurrentNativeEnterCommonOperand.checked_trace_extension workTrace observed.1
  have fields := SourceEqualityNativeDemandAcceptedReadback.work_observation (makeNode rows) (outer + 1)
    middle after result (trace_done outer _ middle after result built)
  have outputFields := node_fields rows middle.native.machine.heap observed.1.machine.1 observed.2.2.1
  have verified := InternedNestedFacts.node_verified rows middle.native.machine.heap
    observed.1.machine.1 observed.2.2.1
  have available : Available after.native.machine.heap result := by
    rw [fields.1, fields.2]
    exact verified.result _ _ rfl
  refine ⟨rows, middle, inner, bounded, walked, observed.2.2.2, observed.1, observed.2.1,
    observed.2.2.1, physicalPrefix, fields.1, fields.2, ?_, ?_, constructorChecked.1,
    observed.2.1.trans constructorChecked.2, available, ?_⟩
  · rw [fields.1]
    exact outputFields.1
  · rw [fields.1]
    exact outputFields.2
  · intro row member
    exact edge_grows _ _ constructorChecked.2.heap row (observed.2.2.1 row member)

end MicroCFTA.SourceCurrentAllocatedNativeRowsPhysicalReadback
