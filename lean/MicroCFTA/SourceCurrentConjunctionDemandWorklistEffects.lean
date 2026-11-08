import MicroCFTA.SourceCurrentConjunctionDemandWorker
import MicroCFTA.SourceCurrentConjunctionDemandEffects
import MicroCFTA.SourceCurrentConjunctionDemandSoundness
import MicroCFTA.SourceCurrentConjunctionDemandWeakEffects

open scoped Classical

/-!
# Physical effects through demand worklists

Every reached admission supplies its actual returned state. The strong
laws retain readiness and clean probes on every outcome. The weak laws
retain their original semantic, coverage, and closed-input premises.
No law supplies the state or the rows of a future admission.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandWorklistEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorker (Physical Table Outcome)

section Strong
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem explore_core (property : Physical Symbol Formula → Prop) (p h budget : Nat)
    (table : SourceCurrentConjunctionWorker.Table Symbol Formula) (pending : List (List Node)) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : ∀ nodes ∈ pending, Values before.heap nodes) (initial : property before)
    (preserve : ∀ budget nodes state, Ready state → Values state.heap nodes → ClosedValues nodes →
      property state → property (SourceCurrentConjunctionDemandAdmission.run p h budget nodes state).state) :
    Effects before (SourceCurrentConjunctionDemandWorker.explore p h budget table pending before).state ∧
      property (SourceCurrentConjunctionDemandWorker.explore p h budget table pending before).state := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil =>
          simpa only [SourceCurrentConjunctionDemandWorker.explore, Outcome.state] using
            And.intro (Effects.refl before ready) initial
      | cons nodes rest tail =>
          rw [SourceCurrentConjunctionDemandWorker.explore.eq_def]
          dsimp only
          split
          · exact tail table before ready (fun group member => inputs group (List.mem_cons_of_mem _ member)) initial
          · split
            · exact tail table before ready (fun group member => inputs group (List.mem_cons_of_mem _ member)) initial
            · have admitted := SourceCurrentConjunctionEmptinessTable.admitted
                SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes
                (Bool.eq_false_iff.mpr (by assumption))
              have closed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
              have first := SourceCurrentConjunctionDemandEffects.run_effects p h budget nodes before ready
                (inputs nodes List.mem_cons_self)
              have safe := preserve budget nodes before ready (inputs nodes List.mem_cons_self) closed initial
              cases actual : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before with
              | failed fault after =>
                  simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state, Outcome.state] using
                    And.intro first safe
              | done result middle =>
                  have kept : Effects before middle := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
                  have current : property middle := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using safe
                  have earlier : ∀ group ∈ rest, Values middle.heap group := by
                    intro group member value included
                    exact kept.keeps.available value (inputs group (List.mem_cons_of_mem _ member) value included)
                  cases result with
                  | overflow =>
                      have later := smaller 0 admitted.1 table rest middle kept.ready earlier current
                      exact ⟨kept.trans later.1, later.2⟩
                  | zero =>
                      have later := tail (⟨nodes, []⟩ :: table) middle kept.ready earlier current
                      exact ⟨kept.trans later.1, later.2⟩
                  | positive predecessor requirements =>
                      have charge := SourceCurrentConjunctionDemandAdmission.positive_charge p h budget nodes before middle
                        predecessor requirements actual
                      have returned := (SourceCurrentConjunctionDemandExecution.admission_graph actual).verified ready
                        (inputs nodes List.mem_cons_self) closed
                      have remaining : ∀ group ∈ requirements.flatten ++ rest, Values middle.heap group := by
                        intro group member
                        rcases List.mem_append.mp member with generated | old
                        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp generated
                          exact (returned.2 row rowIn group groupIn).1
                        · exact earlier group old
                      have later := smaller (budget - (predecessor + 1)) (by omega)
                        (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle kept.ready remaining current
                      exact ⟨kept.trans later.1, later.2⟩

/-- Every exploration outcome retains readiness, records, and equality allocations. -/
theorem explore_effects (p h budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula) (pending : List (List Node))
    (before : Physical Symbol Formula) (ready : Ready before) (inputs : ∀ nodes ∈ pending, Values before.heap nodes) :
    Effects before (SourceCurrentConjunctionDemandWorker.explore p h budget table pending before).state :=
  (explore_core (fun _ => True) p h budget table pending before ready inputs trivial
    (fun _ _ _ _ _ _ _ => trivial)).1

/-- Every exploration outcome retains clean probes at its exact returned heap. -/
theorem explore_probes (p h budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula) (pending : List (List Node))
    (before : Physical Symbol Formula) (ready : Ready before) (probes : ProbeHeap before.heap)
    (inputs : ∀ nodes ∈ pending, Values before.heap nodes) :
    ProbeHeap (SourceCurrentConjunctionDemandWorker.explore p h budget table pending before).state.heap :=
  (explore_core (fun state => ProbeHeap state.heap) p h budget table pending before ready inputs probes
    (fun budget nodes state ready available _ known =>
      SourceCurrentConjunctionDemandEffects.run_probes p h budget nodes state ready known available)).2

private theorem decision_core [DecidableEq Node] (property : Physical Symbol Formula → Prop)
    (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap query) (initial : property before)
    (preserve : ∀ budget nodes state, Ready state → Values state.heap nodes → ClosedValues nodes →
      property state → property (SourceCurrentConjunctionDemandAdmission.run p h budget nodes state).state) :
    Effects before (SourceCurrentConjunctionDemandWorker.decision p h budget query before).state ∧
      property (SourceCurrentConjunctionDemandWorker.decision p h budget query before).state := by
  unfold SourceCurrentConjunctionDemandWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes := by
      intro nodes member value included
      cases List.mem_singleton.mp member
      cases List.mem_singleton.mp included
      exact available
    have first := explore_core property p h budget [] [[query]] before ready inputs initial preserve
    cases actual : SourceCurrentConjunctionDemandWorker.explore p h budget [] [[query]] before with
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | done table after =>
        simp only [actual, Outcome.state] at first
        simp only [Outcome.bind]
        split <;> exact first
  · exact ⟨Effects.refl before ready, initial⟩

/-- The free-list guard and all fixed-point outcomes retain physical effects. -/
theorem decision_effects [DecidableEq Node] (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap query) :
    Effects before (SourceCurrentConjunctionDemandWorker.decision p h budget query before).state :=
  (decision_core (fun _ => True) p h budget query before ready available trivial
    (fun _ _ _ _ _ _ _ => trivial)).1

/-- Decisions retain clean probes on both successful and failed outcomes. -/
theorem decision_probes [DecidableEq Node] (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Available before.heap query) :
    ProbeHeap (SourceCurrentConjunctionDemandWorker.decision p h budget query before).state.heap :=
  (decision_core (fun state => ProbeHeap state.heap) p h budget query before ready available probes
    (fun budget nodes state ready available _ known =>
      SourceCurrentConjunctionDemandEffects.run_probes p h budget nodes state ready known available)).2
end Strong

section Weak
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- Weak exploration needs no equality validity, cost heap, or full readiness. -/
theorem weak_explore_effects (p h budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula) (pending : List (List Node))
    (before : Physical Symbol Formula) (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (inputs : ∀ nodes ∈ pending, Values before.heap nodes ∧ ClosedValues nodes) :
    let actual := SourceCurrentConjunctionDemandWorker.explore p h budget table pending before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil =>
          simp only [SourceCurrentConjunctionDemandWorker.explore, Outcome.state]
          exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
      | cons nodes rest tail =>
          rw [SourceCurrentConjunctionDemandWorker.explore.eq_def]
          dsimp only
          split
          · exact tail table before semantic covered (fun group member => inputs group (List.mem_cons_of_mem _ member))
          · split
            · exact tail table before semantic covered (fun group member => inputs group (List.mem_cons_of_mem _ member))
            · have admitted := SourceCurrentConjunctionEmptinessTable.admitted
                SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes
                (Bool.eq_false_iff.mpr (by assumption))
              have first := SourceCurrentConjunctionDemandWeakEffects.admission_effects p h budget nodes before semantic
                covered (inputs nodes List.mem_cons_self).1 (inputs nodes List.mem_cons_self).2
              cases actual : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before with
              | failed fault after =>
                  simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
                  exact ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1⟩
              | done result middle =>
                  simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
                  rcases first with ⟨semantic, covered, growth, history, returned⟩
                  have earlier : ∀ group ∈ rest, Values middle.heap group ∧ ClosedValues group := by
                    intro group member
                    exact ⟨fun value included => ((inputs group (List.mem_cons_of_mem _ member)).1 value included).grows
                      before.heap middle.heap growth history, (inputs group (List.mem_cons_of_mem _ member)).2⟩
                  cases result with
                  | overflow =>
                      have later := smaller 0 admitted.1 table rest middle semantic covered earlier
                      exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1, extends_trans history later.2.2.2⟩
                  | zero =>
                      have later := tail (⟨nodes, []⟩ :: table) middle semantic covered earlier
                      exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1, extends_trans history later.2.2.2⟩
                  | positive predecessor requirements =>
                      have charge := SourceCurrentConjunctionDemandAdmission.positive_charge p h budget nodes before middle
                        predecessor requirements actual
                      have remaining : ∀ group ∈ requirements.flatten ++ rest, Values middle.heap group ∧ ClosedValues group := by
                        intro group member
                        rcases List.mem_append.mp member with generated | old
                        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp generated
                          exact returned row rowIn group groupIn
                        · exact earlier group old
                      have later := smaller (budget - (predecessor + 1)) (by omega)
                        (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle semantic covered remaining
                      exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1, extends_trans history later.2.2.2⟩

/-- The actual decision retains the weak physical contract on every outcome. -/
theorem weak_decision_effects (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    let actual := SourceCurrentConjunctionDemandWorker.decision p h budget query before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  unfold SourceCurrentConjunctionDemandWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes ∧ ClosedValues nodes := by
      intro nodes member
      cases List.mem_singleton.mp member
      constructor
      · intro value included; cases List.mem_singleton.mp included; exact available
      · intro value included; cases List.mem_singleton.mp included; exact closed
    have first := weak_explore_effects p h budget [] [[query]] before semantic covered inputs
    cases actual : SourceCurrentConjunctionDemandWorker.explore p h budget [] [[query]] before with
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | done table after =>
        simp only [actual, Outcome.state] at first
        simp only [Outcome.bind]
        split <;> exact first
  · exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
end Weak

section Calls
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Memo hits and every miss outcome retain physical readiness and old records. -/
theorem call_effects (p h budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query : Node)
    (before : Physical Symbol FullSyntax.Formula) (ready : Ready before) (available : Available before.heap query) :
    Effects before (SourceCurrentConjunctionDemandWorker.call p h budget memo query before).state := by
  unfold SourceCurrentConjunctionDemandWorker.call
  split
  · exact Effects.refl before ready
  · have first := decision_effects p h budget query before ready available
    cases actual : SourceCurrentConjunctionDemandWorker.decision p h budget query before <;>
      simpa only [actual, Outcome.bind, Outcome.state] using first

/-- Every fourth-memo outcome retains clean stored probes. -/
theorem call_probes (p h budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query : Node)
    (before : Physical Symbol FullSyntax.Formula) (ready : Ready before)
    (probes : ProbeHeap before.heap) (available : Available before.heap query) :
    ProbeHeap (SourceCurrentConjunctionDemandWorker.call p h budget memo query before).state.heap := by
  unfold SourceCurrentConjunctionDemandWorker.call
  split
  · exact probes
  · have first := decision_probes p h budget query before ready probes available
    cases actual : SourceCurrentConjunctionDemandWorker.decision p h budget query before <;>
      simpa only [actual, Outcome.bind, Outcome.state] using first
end Calls

/-- Weak fourth-memo effects require neither equality validity nor a cost heap. -/
theorem weak_call_effects (p h budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo)
    (query : Value SourcePruningTemplates.Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (before : Physical SourcePruningTemplates.Symbol FullSyntax.Formula)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before.heap)
    (covered : Covered [] before.heap) (available : Available before.heap query) (closed : query.free = []) :
    let actual := SourceCurrentConjunctionDemandWorker.call p h budget memo query before
    SourceRecursiveIntersectionSemanticHeap.SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧
      Grows before.heap actual.state.heap ∧ Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  unfold SourceCurrentConjunctionDemandWorker.call
  split
  · exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
  · have first := weak_decision_effects p h budget query before semantic covered available closed
    cases actual : SourceCurrentConjunctionDemandWorker.decision p h budget query before <;>
      simpa only [actual, Outcome.bind, Outcome.state] using first

end MicroCFTA.SourceCurrentConjunctionDemandWorklistEffects
