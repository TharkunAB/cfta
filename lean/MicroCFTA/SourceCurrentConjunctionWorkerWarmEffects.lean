import MicroCFTA.SourceCurrentConjunctionWorkerEffects
import MicroCFTA.SourceCurrentConjunctionRowsWarmEffects

set_option autoImplicit false
open scoped Classical

/-! Full readiness at every actual conjunction-call outcome. -/
namespace MicroCFTA.SourceCurrentConjunctionWorkerWarmEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionWorker
open SourceCurrentConjunctionRowsAllocation (Ready Effects)

section Generic
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Every actual exploration outcome retains full physical readiness. -/
theorem explore_effects (p h budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula)
    (pending : List (List (Value Symbol Guard))) (before : Physical Symbol Formula)
    (ready : Ready before)
    (inputs : ∀ nodes ∈ pending, Values before.heap nodes ∧ ClosedValues nodes) :
    Effects before (SourceCurrentConjunctionWorker.explore p h budget table pending before).state := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
    induction pending generalizing table before with
    | nil =>
      simpa only [SourceCurrentConjunctionWorker.explore, Outcome.state] using Effects.refl before ready
    | cons nodes rest tail =>
      rw [SourceCurrentConjunctionWorker.explore]
      split
      · exact tail table before ready
          (fun group member => inputs group (List.mem_cons_of_mem _ member))
      · split
        · exact tail table before ready
            (fun group member => inputs group (List.mem_cons_of_mem _ member))
        · have positive := (SourceCurrentConjunctionEmptinessTable.admitted
            SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed
            budget table nodes (Bool.eq_false_iff.mpr (by assumption))).1
          have first : Effects before (SourceCurrentConjunctionRowsWorker.rows p h nodes before).state :=
            Eq.mp (by congr <;> exact Subsingleton.elim _ _)
              (SourceCurrentConjunctionRowsWarmEffects.rows_effects p h nodes before ready
                (inputs nodes List.mem_cons_self).1)
          have returned := (SourceCurrentConjunctionRowsWorkerEffects.rows_effects p h nodes before
            ready.semantic.ready.semantic ready.semantic.ready.covered
            (inputs nodes List.mem_cons_self).1 (inputs nodes List.mem_cons_self).2).2.2.2.2
          cases actual : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
          | done requirements middle =>
            simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
            rw [actual] at returned
            have remaining : ∀ group ∈ requirements.flatten ++ rest,
                Values middle.heap group ∧ ClosedValues group := by
              intro group member
              rcases List.mem_append.mp member with fresh | old
              · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp fresh
                exact returned row rowIn group groupIn
              · exact ⟨fun value included => first.keeps.available value
                    ((inputs group (List.mem_cons_of_mem _ old)).1 value included),
                  (inputs group (List.mem_cons_of_mem _ old)).2⟩
            exact first.trans (smaller (budget - 1) (by omega) (⟨nodes, requirements⟩ :: table)
              (requirements.flatten ++ rest) middle first.ready remaining)
          | failed fault after =>
            simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state, Outcome.state] using first

/-- Both fixed-point outcomes retain the full actual explored physical state. -/
theorem decision_effects (p h budget : Nat) (query : Value Symbol Guard)
    (before : Physical Symbol Formula) (ready : Ready before)
    (available : Available before.heap query) (closed : query.free = []) :
    Effects before (SourceCurrentConjunctionWorker.decision p h budget query before).state := by
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
    have explored := explore_effects p h budget [] [[query]] before ready inputs
    cases actual : SourceCurrentConjunctionWorker.explore p h budget [] [[query]] before with
    | failed fault after =>
      simpa only [actual, Outcome.bind, Outcome.state] using explored
    | done table after =>
      simp only [actual, Outcome.state] at explored
      simp only [Outcome.bind]
      split <;> exact explored
  · exact Effects.refl before ready
end Generic

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula

/-- Memo hits and every actual miss outcome retain full physical readiness. -/
theorem call_effects (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) (closed : query.free = []) :
    Effects before (SourceCurrentConjunctionWorker.call p h budget memo query before).state := by
  unfold SourceCurrentConjunctionWorker.call
  split
  · exact Effects.refl before ready
  · have decided := decision_effects p h budget query before ready available closed
    cases actual : SourceCurrentConjunctionWorker.decision p h budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using decided
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using decided

/-- The allocated call retains full readiness at its literal returned physical state. -/
theorem allocated_call_effects {width : Nat} (p h budget : Nat) (memo : Memo)
    (query : Node) (before : SourceEqualityNativeDemand.State width)
    (ready : Ready (SourceCurrentAllocatedNativeEffects.physical before))
    (available : Available before.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo
    Effects (SourceCurrentAllocatedNativeEffects.physical before)
      (SourceCurrentAllocatedNativeEffects.physical actual.state) := by
  have first := call_effects p h budget memo query
    (SourceCurrentAllocatedNativeEffects.physical before) ready available closed
  cases actual : SourceCurrentConjunctionWorker.call p h budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before) with
  | done output after =>
    rcases output with ⟨answer, saved⟩
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at first
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state,
      SourceCurrentAllocatedQueryMemo.physical_advance] using first
  | failed fault after =>
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at first
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state,
      SourceCurrentAllocatedQueryMemo.physical_advance] using first

end MicroCFTA.SourceCurrentConjunctionWorkerWarmEffects
