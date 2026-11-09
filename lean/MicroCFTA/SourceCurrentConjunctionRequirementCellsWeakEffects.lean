import MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed
import MicroCFTA.SourceEqualityProjectionWorkerEffects

/-!
# Weak physical effects of actual shared-cell forcing

Semantic heaps, closed coverage, and current resident closed cells supply
every projection. All force outcomes retain both cell invariants and the
exact reached heap. Successful forces return resident closed nodes. Costs
and equality-operation readiness are not premises. The symbol alphabet is
the actual source alphabet used by both checked callers.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsWeakEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionRequirementCells
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "Job" => SourceCurrentConjunctionRowsWorker.Job Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "ValuesInvariant" => SourceCurrentConjunctionRequirementCellsValues.Invariant
local notation "ClosedInvariant" => SourceCurrentConjunctionRequirementCellsClosed.Invariant
local notation "CellValues" => SourceCurrentConjunctionRequirementCellsValues.CellValues
local notation "CellClosed" => SourceCurrentConjunctionRequirementCellsClosed.CellClosed

private structure HeapEffects (before after : Physical) : Prop where
  semantic : SemanticHeap after.heap
  covered : Covered [] after.heap
  growth : Grows before.heap after.heap
  history : Extends before.heap.nodes.issued after.heap.nodes.issued

private theorem refl_effects (before : Physical) (semantic : SemanticHeap before.heap)
    (covered : Covered [] before.heap) : HeapEffects before before :=
  ⟨semantic, covered, grows_refl _, extends_refl _⟩

private theorem values_grows (before : Cells) (after : Physical)
    (growth : Grows before.physical.heap after.heap)
    (history : Extends before.physical.heap.nodes.issued after.heap.nodes.issued)
    (values : ValuesInvariant before) : ValuesInvariant {before with physical := after} := by
  intro handle cell found
  have own := values handle cell found
  cases cell with
  | column nodes | done nodes =>
      intro value member
      exact (own value member).grows _ _ growth history
  | pending cursor =>
      exact ⟨fun value member => (own.1 value member).grows _ _ growth history,
        fun job member value included => (own.2 job member value included).grows _ _ growth history⟩

private theorem update_values (handle : Nat) (original replacement : Cell Symbol Formula) (before : Cells)
    (found : lookup handle before = some original) (values : ValuesInvariant before)
    (own : CellValues before.physical.heap replacement) : ValuesInvariant (update handle replacement before) := by
  intro other cell present
  by_cases same : other = handle
  · subst other
    have inserted := lookup_update handle original replacement before found
    have equal : replacement = cell := Option.some.inj (inserted.symm.trans present)
    exact equal ▸ own
  · have retained : lookup other (update handle replacement before) = lookup other before :=
      List.getElem?_set_ne (Ne.symm same)
    exact values other cell (retained.symm.trans present)

private theorem update_closed (handle : Nat) (original replacement : Cell Symbol Formula) (before : Cells)
    (found : lookup handle before = some original) (closed : ClosedInvariant before)
    (own : CellClosed replacement) : ClosedInvariant (update handle replacement before) := by
  intro other cell present
  by_cases same : other = handle
  · subst other
    have inserted := lookup_update handle original replacement before found
    have equal : replacement = cell := Option.some.inj (inserted.symm.trans present)
    exact equal ▸ own
  · have retained : lookup other (update handle replacement before) = lookup other before :=
      List.getElem?_set_ne (Ne.symm same)
    exact closed other cell (retained.symm.trans present)

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection_effects (p h : Nat) (job : Job) (before : Physical)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Values before.heap job.1) (closed : ClosedValues job.1) :
    HeapEffects before (SourceCurrentConjunctionRequirementPull.projection p h job before).state ∧
      ∀ value after, SourceCurrentConjunctionRequirementPull.projection p h job before =
        .done value after → Available after.heap value ∧ value.free = [] := by
  rcases job with ⟨forest, path⟩
  let currentEquality : DecidableEq (EdgeKey Symbol Guard) := inferInstance
  have native := SourceEqualityProjectionWorkerPhysical.forest_effects
    p h (path.map Int.ofNat) forest before.heap semantic covered available closed
  have same (other : DecidableEq (EdgeKey Symbol Guard)) :
      @SourceEqualityProjectionWorker.forest Symbol Guard other
        p h (path.map Int.ofNat) forest before.heap =
      @SourceEqualityProjectionWorker.forest Symbol Guard currentEquality
        p h (path.map Int.ofNat) forest before.heap :=
    congrArg (fun equality => @SourceEqualityProjectionWorker.forest Symbol Guard equality
      p h (path.map Int.ofNat) forest before.heap) (Subsingleton.elim other currentEquality)
  rw [same] at native
  cases actual : @SourceEqualityProjectionWorker.forest Symbol Guard currentEquality
      p h (path.map Int.ofNat) forest before.heap with
  | done value heap =>
      simp only [actual, SourceEqualityProjectionWorkerPhysical.reached] at native
      simp only [SourceCurrentConjunctionRequirementPull.projection, SourceCurrentConjunctionRowsWorker.projections,
        actual, SourceCurrentConjunctionRowsWorker.Outcome.bind, List.headD_cons,
        SourceCurrentConjunctionRowsWorker.Outcome.state]
      exact ⟨⟨native.1, native.2.1, native.2.2.1, native.2.2.2.1⟩,
        by intro result after same; cases same; exact native.2.2.2.2⟩
  | pending key heap | unresolved name heap | exhausted limit heap =>
      simp only [actual, SourceEqualityProjectionWorkerPhysical.reached] at native
      simp only [SourceCurrentConjunctionRequirementPull.projection, SourceCurrentConjunctionRowsWorker.projections,
        actual, SourceCurrentConjunctionRowsWorker.Outcome.bind, SourceCurrentConjunctionRowsWorker.Outcome.state]
      exact ⟨⟨native.1, native.2.1, native.2.2.1, native.2.2.2.1⟩,
        by intro value after impossible; cases impossible⟩

private structure StepPost (before : Cells) (actual : Outcome Symbol Formula (Event Symbol Formula)) : Prop where
  effects : HeapEffects before.physical actual.state.physical
  values : ValuesInvariant actual.state
  closed : ClosedInvariant actual.state
  finished : ∀ event after, actual = .done event after →
    SourceCurrentConjunctionRequirementCellsValues.EventValues after.physical.heap event ∧
      SourceCurrentConjunctionRequirementCellsClosed.EventClosed event

omit [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem done_post (before after : Cells) (event : Event Symbol Formula)
    (effects : HeapEffects before.physical after.physical) (values : ValuesInvariant after)
    (closed : ClosedInvariant after)
    (result : SourceCurrentConjunctionRequirementCellsValues.EventValues after.physical.heap event ∧
      SourceCurrentConjunctionRequirementCellsClosed.EventClosed event) : StepPost before (.done event after) :=
  ⟨effects, values, closed, by intro output final same; cases same; exact result⟩

private theorem step_effects (p h handle : Nat) (before : Cells)
    (semantic : SemanticHeap before.physical.heap) (covered : Covered [] before.physical.heap)
    (values : ValuesInvariant before) (closed : ClosedInvariant before) :
    StepPost before (forceStep p h handle before) := by
  cases found : lookup handle before with
  | none =>
      simp only [forceStep, found]
      exact ⟨refl_effects _ semantic covered, values, closed, by intro event after impossible; cases impossible⟩
  | some cell =>
      cases cell with
      | done nodes =>
          simp only [forceStep, found]
          exact done_post before before (.complete nodes) (refl_effects _ semantic covered) values closed
            ⟨values handle _ found, closed handle _ found⟩
      | column nodes =>
          simp only [forceStep, found]
          have resident := SourceCurrentConjunctionRequirementCellsValues.canonical_available nodes before.physical.heap
            (values handle _ found)
          have finalClosed := SourceCurrentConjunctionRequirementCellsClosed.canonical_closed nodes (closed handle _ found)
          exact done_post before _ _ (refl_effects _ semantic covered)
            (update_values handle _ _ before found values resident)
            (update_closed handle _ _ before found closed finalClosed) ⟨resident, finalClosed⟩
      | pending cursor =>
          rcases cursor with ⟨jobs, collected⟩
          have own := values handle (.pending ⟨jobs, collected⟩) found
          have ownClosed := closed handle (.pending ⟨jobs, collected⟩) found
          cases jobs with
          | nil =>
              simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step]
              have resident := SourceCurrentConjunctionRequirementCellsValues.canonical_available collected
                before.physical.heap own.1
              have finalClosed := SourceCurrentConjunctionRequirementCellsClosed.canonical_closed collected ownClosed.1
              exact done_post before _ _ (refl_effects _ semantic covered)
                (update_values handle _ _ before found values resident)
                (update_closed handle _ _ before found closed finalClosed) ⟨resident, finalClosed⟩
          | cons job rest =>
              have first := projection_effects p h job before.physical semantic covered
                (own.2 job List.mem_cons_self) (ownClosed.2 job List.mem_cons_self)
              cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before.physical with
              | failed fault physical =>
                  have kept : HeapEffects before.physical physical := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.1
                  simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                    SourceCurrentConjunctionRowsWorker.Outcome.bind]
                  exact ⟨kept, values_grows before physical kept.growth kept.history values, closed,
                    by intro event after impossible; cases impossible⟩
              | done value physical =>
                  have kept : HeapEffects before.physical physical := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.1
                  have result := first.2 value physical actual
                  have current := values_grows before physical kept.growth kept.history values
                  cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
                  | true =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, tested, ite_true]
                      have resident : Values physical.heap [(.empty : Node)] := by
                        intro node member
                        cases List.mem_singleton.mp member
                        exact empty_available physical.heap
                      have finalClosed : ClosedValues [(.empty : Node)] := by
                        intro node member
                        cases List.mem_singleton.mp member
                        rfl
                      exact done_post before _ _ kept
                        (update_values handle _ _ {before with physical := physical} found current resident)
                        (update_closed handle _ _ {before with physical := physical} found closed finalClosed)
                        ⟨resident, finalClosed⟩
                  | false =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, tested, Bool.false_eq_true, ite_false]
                      have resident : CellValues physical.heap (.pending ⟨rest, collected ++ [value]⟩) := by
                        constructor
                        · intro node member
                          rcases List.mem_append.mp member with old | new
                          · exact (own.1 node old).grows _ _ kept.growth kept.history
                          · cases List.mem_singleton.mp new
                            exact result.1
                        · intro later member node included
                          exact (own.2 later (List.mem_cons_of_mem _ member) node included).grows _ _ kept.growth kept.history
                      have finalClosed : CellClosed (.pending ⟨rest, collected ++ [value]⟩) := by
                        constructor
                        · intro node member
                          rcases List.mem_append.mp member with old | new
                          · exact ownClosed.1 node old
                          · cases List.mem_singleton.mp new
                            exact result.2
                        · intro later member
                          exact ownClosed.2 later (List.mem_cons_of_mem _ member)
                      exact done_post before _ _ kept
                        (update_values handle _ _ {before with physical := physical} found current resident)
                        (update_closed handle _ _ {before with physical := physical} found closed finalClosed)
                        ⟨resident, finalClosed⟩

/-- All force outcomes retain weak heap effects, closed resident cells, and their successful values. -/
theorem force_effects (p h handle : Nat) (before : Cells)
    (semantic : SemanticHeap before.physical.heap) (covered : Covered [] before.physical.heap)
    (values : ValuesInvariant before) (closed : ClosedInvariant before) :
    let actual := force p h handle before
    SemanticHeap actual.state.physical.heap ∧ Covered [] actual.state.physical.heap ∧
      Grows before.physical.heap actual.state.physical.heap ∧
      Extends before.physical.heap.nodes.issued actual.state.physical.heap.nodes.issued ∧
      ValuesInvariant actual.state ∧ ClosedInvariant actual.state ∧
      ∀ nodes after, actual = .done nodes after → Values after.physical.heap nodes ∧ ClosedValues nodes := by
  suffices ∀ weight (current : Cells), remaining handle current = weight →
      SemanticHeap current.physical.heap → Covered [] current.physical.heap →
      ValuesInvariant current → ClosedInvariant current →
      let actual := force p h handle current
      SemanticHeap actual.state.physical.heap ∧ Covered [] actual.state.physical.heap ∧
        Grows current.physical.heap actual.state.physical.heap ∧
        Extends current.physical.heap.nodes.issued actual.state.physical.heap.nodes.issued ∧
        ValuesInvariant actual.state ∧ ClosedInvariant actual.state ∧
        ∀ nodes after, actual = .done nodes after → Values after.physical.heap nodes ∧ ClosedValues nodes by
    exact this _ before rfl semantic covered values closed
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured semantic covered values closed
      rw [force_step]
      have first := step_effects p h handle current semantic covered values closed
      cases actual : forceStep p h handle current with
      | failed fault after =>
          rw [actual] at first
          exact ⟨first.effects.semantic, first.effects.covered, first.effects.growth, first.effects.history,
            first.values, first.closed, by intro nodes final impossible; cases impossible⟩
      | done event after =>
          rw [actual] at first
          cases event with
          | complete nodes =>
              have result := first.finished _ _ rfl
              exact ⟨first.effects.semantic, first.effects.covered, first.effects.growth, first.effects.history,
                first.values, first.closed, by intro output final same; cases same; exact result⟩
          | more cursor =>
              have decreased : remaining handle after < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current after cursor actual
              obtain ⟨sem, cov, growth, history, finalValues, finalClosed, result⟩ :=
                smaller _ decreased after rfl first.effects.semantic first.effects.covered first.values first.closed
              exact ⟨sem, cov, grows_trans first.effects.growth growth, extends_trans first.effects.history history,
                finalValues, finalClosed, result⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsWeakEffects
