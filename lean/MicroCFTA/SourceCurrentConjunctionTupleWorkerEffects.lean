import MicroCFTA.SourceCurrentConjunctionTupleWorker
import MicroCFTA.SourceCurrentConjunctionTupleAdmissionEffects

set_option autoImplicit false
open scoped Classical

/-!
# Full readiness through physical tuple-budget exploration

The actual admission supplies each reached state. Zero charge removes the
pending head. Positive charge supplies closed available requirements.
Overflow drains the old suffix at zero budget. No returned-state or future
row supplier is assumed. The selected caller and native lazy demand remain
separate attachments.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWorkerEffects
open InternedConstructorTemplates
open InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorker (Physical Table Outcome)
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- Every actual exploration outcome retains readiness, original records, and equality allocations. -/
theorem explore_effects (p h budget : Nat) (table : Table Symbol Formula)
    (pending : List (List Node)) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : ∀ nodes ∈ pending, Values before.heap nodes) :
    Effects before (SourceCurrentConjunctionTupleWorker.explore p h budget table pending before).state := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
    induction pending generalizing table before with
    | nil =>
        simpa only [SourceCurrentConjunctionTupleWorker.explore, Outcome.state] using Effects.refl before ready
    | cons nodes rest tail =>
        rw [SourceCurrentConjunctionTupleWorker.explore.eq_def]
        dsimp only
        split
        · exact tail table before ready (fun group member => inputs group (List.mem_cons_of_mem _ member))
        · split
          · exact tail table before ready (fun group member => inputs group (List.mem_cons_of_mem _ member))
          · have admitted := SourceCurrentConjunctionEmptinessTable.admitted
              SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes
              (Bool.eq_false_iff.mpr (by assumption))
            have first : Effects before
                (SourceCurrentConjunctionTupleAdmission.run p h budget nodes before).state :=
              Eq.mp (by congr <;> exact Subsingleton.elim _ _)
                (SourceCurrentConjunctionTupleAdmissionEffects.run_effects p h budget nodes before ready
                  (inputs nodes List.mem_cons_self))
            cases actual : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before with
            | failed fault after =>
                simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state, Outcome.state] using first
            | done result middle =>
                have kept : Effects before middle := by
                  simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
                have oldInputs : ∀ group ∈ rest, Values middle.heap group := by
                  intro group member value included
                  exact kept.keeps.available value (inputs group (List.mem_cons_of_mem _ member) value included)
                cases result with
                | overflow =>
                    exact kept.trans (smaller 0 admitted.1 table rest middle kept.ready oldInputs)
                | zero =>
                    exact kept.trans (tail (⟨nodes, []⟩ :: table) middle kept.ready oldInputs)
                | positive predecessor requirements =>
                    have charge := SourceCurrentConjunctionTupleAdmission.positive_charge p h budget nodes before middle
                      predecessor requirements actual
                    have returned := SourceCurrentConjunctionTupleAdmissionEffects.positive_closed p h budget nodes before middle
                      predecessor requirements ready (inputs nodes List.mem_cons_self)
                      (SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1) actual
                    have remaining : ∀ group ∈ requirements.flatten ++ rest, Values middle.heap group := by
                      intro group member
                      rcases List.mem_append.mp member with fresh | old
                      · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp fresh
                        exact (returned row rowIn group groupIn).1
                      · exact oldInputs group old
                    exact kept.trans (smaller (budget - (predecessor + 1)) (by omega)
                      (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle kept.ready remaining)

/-- The closed guard and both fixed-point outcomes retain the actual explored physical state. -/
theorem decision_effects (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap query) :
    Effects before (SourceCurrentConjunctionTupleWorker.decision p h budget query before).state := by
  unfold SourceCurrentConjunctionTupleWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes := by
      intro nodes member
      have same := List.mem_singleton.mp member
      subst nodes
      intro value included
      simpa only [List.mem_singleton.mp included] using available
    have first := explore_effects p h budget [] [[query]] before ready inputs
    cases actual : SourceCurrentConjunctionTupleWorker.explore p h budget [] [[query]] before with
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | done table after =>
        simp only [actual, Outcome.state] at first
        simp only [Outcome.bind]
        split <;> exact first
  · exact Effects.refl before ready

/-- Hits and all miss outcomes retain full readiness and old physical records. -/
theorem call_effects (p h budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo)
    (query : Value SourcePruningTemplates.Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (before : Physical SourcePruningTemplates.Symbol FullSyntax.Formula)
    (ready : Ready before) (available : Available before.heap query) :
    Effects before (SourceCurrentConjunctionTupleWorker.call p h budget memo query before).state := by
  unfold SourceCurrentConjunctionTupleWorker.call
  split
  · exact Effects.refl before ready
  · have first := decision_effects p h budget query before ready available
    cases actual : SourceCurrentConjunctionTupleWorker.decision p h budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first

end MicroCFTA.SourceCurrentConjunctionTupleWorkerEffects
