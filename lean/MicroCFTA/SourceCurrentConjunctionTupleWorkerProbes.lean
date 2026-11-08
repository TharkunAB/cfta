import MicroCFTA.SourceCurrentConjunctionTupleWorkerEffects

set_option autoImplicit false
open scoped Classical

/-!
# Clean recursive probes through every tuple-worker outcome

The proof follows each reached admission and its actual returned state.
Overflow and zero retain exposure probes. Positive admission supplies clean
probes and available requirements to the recursive call. Failed outcomes and
memo hits retain the same property. Native demand remains a separate boundary.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWorkerProbes
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorker (Physical Table Outcome)
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

/-- Every actual exploration outcome retains clean stored recursive probes. -/
theorem explore_probes (p h budget : Nat) (table : Table Symbol Formula)
    (pending : List (List Node)) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : ProbeHeap before.heap)
    (inputs : ∀ nodes ∈ pending, Values before.heap nodes) :
    ProbeHeap (SourceCurrentConjunctionTupleWorker.explore p h budget table pending before).state.heap := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
    induction pending generalizing table before with
    | nil => simpa only [SourceCurrentConjunctionTupleWorker.explore, Outcome.state] using probes
    | cons nodes rest tail =>
        rw [SourceCurrentConjunctionTupleWorker.explore.eq_def]
        dsimp only
        split
        · exact tail table before ready probes (fun group member => inputs group (List.mem_cons_of_mem _ member))
        · split
          · exact tail table before ready probes (fun group member => inputs group (List.mem_cons_of_mem _ member))
          · have admitted := SourceCurrentConjunctionEmptinessTable.admitted
              SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes
              (Bool.eq_false_iff.mpr (by assumption))
            have first : Effects before
                (SourceCurrentConjunctionTupleAdmission.run p h budget nodes before).state :=
              Eq.mp (by congr <;> exact Subsingleton.elim _ _)
                (SourceCurrentConjunctionTupleAdmissionEffects.run_effects p h budget nodes before ready
                  (inputs nodes List.mem_cons_self))
            have clean : ProbeHeap (SourceCurrentConjunctionTupleAdmission.run p h budget nodes before).state.heap :=
              Eq.mp (by congr <;> exact Subsingleton.elim _ _)
                (SourceCurrentConjunctionTupleAdmissionEffects.run_probes p h budget nodes before ready probes
                  (inputs nodes List.mem_cons_self))
            cases actual : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before with
            | failed fault after =>
                simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state, Outcome.state] using clean
            | done result middle =>
                have kept : Effects before middle := by
                  simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
                have warm : ProbeHeap middle.heap := by
                  simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using clean
                have oldInputs : ∀ group ∈ rest, Values middle.heap group := by
                  intro group member value included
                  exact kept.keeps.available value (inputs group (List.mem_cons_of_mem _ member) value included)
                cases result with
                | overflow => exact smaller 0 admitted.1 table rest middle kept.ready warm oldInputs
                | zero => exact tail (⟨nodes, []⟩ :: table) middle kept.ready warm oldInputs
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
                    exact smaller (budget - (predecessor + 1)) (by omega)
                      (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle kept.ready warm remaining

/-- Every actual decision outcome retains clean probes, including fixed-point failure. -/
theorem decision_probes (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Available before.heap query) :
    ProbeHeap (SourceCurrentConjunctionTupleWorker.decision p h budget query before).state.heap := by
  unfold SourceCurrentConjunctionTupleWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes := by
      intro nodes member
      have same := List.mem_singleton.mp member
      subst nodes
      intro value included
      simpa only [List.mem_singleton.mp included] using available
    have first := explore_probes p h budget [] [[query]] before ready probes inputs
    cases actual : SourceCurrentConjunctionTupleWorker.explore p h budget [] [[query]] before with
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | done table after =>
        simp only [actual, Outcome.state] at first
        simp only [Outcome.bind]
        split <;> exact first
  · exact probes

/-- Hits and every miss outcome retain clean probes in the actual returned heap. -/
theorem call_probes (p h budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo)
    (query : Value SourcePruningTemplates.Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (before : Physical SourcePruningTemplates.Symbol FullSyntax.Formula)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Available before.heap query) :
    ProbeHeap (SourceCurrentConjunctionTupleWorker.call p h budget memo query before).state.heap := by
  unfold SourceCurrentConjunctionTupleWorker.call
  split
  · exact probes
  · have first := decision_probes p h budget query before ready probes available
    cases actual : SourceCurrentConjunctionTupleWorker.decision p h budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first

end MicroCFTA.SourceCurrentConjunctionTupleWorkerProbes
