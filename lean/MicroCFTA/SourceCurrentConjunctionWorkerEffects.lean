import MicroCFTA.SourceCurrentConjunctionWorker
import MicroCFTA.SourceCurrentAllocatedConjunctionWorker
import MicroCFTA.SourceCurrentConjunctionRowsWorkerEffects

set_option autoImplicit false
open scoped Classical

/-! Physical effects of actual current conjunction calls. -/
namespace MicroCFTA.SourceCurrentConjunctionWorkerEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionWorker

section Generic
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Every actual exploration outcome retains constructor heap effects. -/
theorem explore_effects (p h budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula)
    (pending : List (List (Value Symbol Guard))) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (inputs : ∀ nodes ∈ pending, Values before.heap nodes ∧ ClosedValues nodes) :
    let actual := SourceCurrentConjunctionWorker.explore p h budget table pending before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧
      Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
    induction pending generalizing table before with
    | nil =>
      simp only [SourceCurrentConjunctionWorker.explore, Outcome.state]
      exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
    | cons nodes rest tail =>
      rw [SourceCurrentConjunctionWorker.explore]
      split
      · exact tail table before semantic covered
          (fun group member => inputs group (List.mem_cons_of_mem _ member))
      · split
        · exact tail table before semantic covered
            (fun group member => inputs group (List.mem_cons_of_mem _ member))
        · have positive := (SourceCurrentConjunctionEmptinessTable.admitted
            SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed
            budget table nodes (Bool.eq_false_iff.mpr (by assumption))).1
          have first := SourceCurrentConjunctionRowsWorkerEffects.rows_effects p h nodes before
            semantic covered (inputs nodes List.mem_cons_self).1 (inputs nodes List.mem_cons_self).2
          cases actual : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
          | done requirements middle =>
            simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
            rcases first with ⟨sem, cov, growth, history, returned⟩
            have remaining : ∀ group ∈ requirements.flatten ++ rest,
                Values middle.heap group ∧ ClosedValues group := by
              intro group member
              rcases List.mem_append.mp member with fresh | old
              · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp fresh
                exact returned row rowIn group groupIn
              · exact ⟨fun value included => ((inputs group (List.mem_cons_of_mem _ old)).1
                    value included).grows before.heap middle.heap growth history,
                  (inputs group (List.mem_cons_of_mem _ old)).2⟩
            have reached := smaller (budget - 1) (by omega) (⟨nodes, requirements⟩ :: table)
              (requirements.flatten ++ rest) middle sem cov remaining
            exact ⟨reached.1, reached.2.1, grows_trans growth reached.2.2.1,
              extends_trans history reached.2.2.2⟩
          | failed fault after =>
            simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
            exact ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1⟩

/-- Open inputs and both fixed-point outcomes retain the actual explored heap. -/
theorem decision_effects (p h budget : Nat)
    (query : Value Symbol Guard) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    let actual := SourceCurrentConjunctionWorker.decision p h budget query before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧
      Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  unfold SourceCurrentConjunctionWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes ∧ ClosedValues nodes := by
      intro nodes member
      have same := List.mem_singleton.mp member
      subst nodes
      constructor
      · intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact available
      · intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact closed
    have explored := explore_effects p h budget [] [[query]] before semantic covered inputs
    cases actual : SourceCurrentConjunctionWorker.explore p h budget [] [[query]] before with
    | failed fault after =>
      simpa only [actual, Outcome.bind, Outcome.state] using explored
    | done table after =>
      simp only [actual, Outcome.state] at explored
      simp only [Outcome.bind]
      split <;> exact explored
  · exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
end Generic

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula

/-- Memo hits and both actual miss outcomes retain constructor heap effects. -/
theorem call_effects (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    let actual := SourceCurrentConjunctionWorker.call p h budget memo query before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧
      Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  unfold SourceCurrentConjunctionWorker.call
  split
  · exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
  · have decided := decision_effects p h budget query before semantic covered available closed
    cases actual : SourceCurrentConjunctionWorker.decision p h budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using decided
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using decided

/-- The allocated call retains its literal physical endpoint on success and failure. -/
theorem allocated_call_effects {width : Nat} (p h budget : Nat) (memo : Memo)
    (query : Node) (before : SourceEqualityNativeDemand.State width)
    (semantic : SemanticHeap before.native.machine.heap)
    (covered : Covered [] before.native.machine.heap)
    (available : Available before.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo
    SemanticHeap actual.state.native.machine.heap ∧ Covered [] actual.state.native.machine.heap ∧
      Grows before.native.machine.heap actual.state.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued actual.state.native.machine.heap.nodes.issued := by
  have first := call_effects p h budget memo query
    (SourceCurrentAllocatedNativeEffects.physical before) semantic covered available closed
  cases actual : SourceCurrentConjunctionWorker.call p h budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before) with
  | done output after =>
    rcases output with ⟨answer, saved⟩
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at first
    simp only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state, SourceCurrentAllocatedQueryMemo.advancePhysical]
    exact first
  | failed fault after =>
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at first
    simp only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state, SourceCurrentAllocatedQueryMemo.advancePhysical]
    exact first

end MicroCFTA.SourceCurrentConjunctionWorkerEffects
