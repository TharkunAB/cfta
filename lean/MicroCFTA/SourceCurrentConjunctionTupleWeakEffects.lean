import MicroCFTA.SourceCurrentConjunctionTupleWorker
import MicroCFTA.SourceCurrentConjunctionRowsWorkerEffects

set_option autoImplicit false
open scoped Classical

/-!
# Weak physical effects of actual tuple-budget execution

Semantic heap facts, closed coverage, and resident closed operands supply
every reached operation. The result retains semantic heap facts, coverage,
constructor growth, and issued identities. Positive admission also supplies
resident closed requirements. Equality-cache validity, costs, and operation
field validity are not premises of these heap laws.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWeakEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionWorker (Physical Table Outcome)
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

private theorem exposures_effects (h : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    let actual := SourceCurrentConjunctionRowsWorker.exposures h nodes before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  induction nodes generalizing before with
  | nil =>
      simpa only [SourceCurrentConjunctionRowsWorker.exposures, SourceCurrentConjunctionRowsWorker.Outcome.state] using
        (show SemanticHeap before.heap ∧ Covered [] before.heap ∧ Grows before.heap before.heap ∧
          Extends before.heap.nodes.issued before.heap.nodes.issued from
          ⟨semantic, covered, grows_refl _, extends_refl _⟩)
  | cons value nodes ih =>
      have first := MergedFreshOrdinaryColdEffects.nodeEdges_verified h value before.heap semantic covered
        (available value List.mem_cons_self) (closed value List.mem_cons_self)
      cases actual : MergedFreshOrdinaryExposure.nodeEdges h value before.heap with
      | done edges heap =>
          rw [actual] at first
          have later := ih (⟨heap, before.equality⟩ : Physical Symbol Formula) first.semantic first.covered
            (fun child member => (available child (List.mem_cons_of_mem _ member)).grows
              before.heap heap first.growth first.history)
            (fun child member => closed child (List.mem_cons_of_mem _ member))
          simp only [SourceCurrentConjunctionRowsWorker.exposures, actual]
          cases tail : SourceCurrentConjunctionRowsWorker.exposures h nodes ⟨heap, before.equality⟩ <;>
            simp only [tail, SourceCurrentConjunctionRowsWorker.Outcome.bind,
              SourceCurrentConjunctionRowsWorker.Outcome.state] at later ⊢ <;>
            exact ⟨later.1, later.2.1, grows_trans first.growth later.2.2.1,
              extends_trans first.history later.2.2.2⟩
      | pending key heap | unresolved key heap =>
          rw [actual] at first
          exact False.elim first.outcome
      | exhausted heap =>
          rw [actual] at first
          simp only [SourceCurrentConjunctionRowsWorker.exposures, actual,
            SourceCurrentConjunctionRowsWorker.Outcome.state]
          exact ⟨first.semantic, first.covered, first.growth, first.history⟩

/-- All admission outcomes retain weak heap effects. Positive rows have resident closed operands. -/
theorem admission_effects (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    let actual := SourceCurrentConjunctionTupleAdmission.run p h budget nodes before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued ∧
      match actual with
      | .done (.positive _ requirements) after =>
          ∀ row ∈ requirements, ∀ operands ∈ row, Values after.heap operands ∧ ClosedValues operands
      | _ => True := by
  have first := exposures_effects h nodes before semantic covered available closed
  cases read : SourceCurrentConjunctionRowsWorker.exposures h nodes before with
  | failed fault exposed =>
      simp only [read, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
      simp only [SourceCurrentConjunctionTupleAdmission.run, read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind, SourceCurrentConjunctionRowsWorker.Outcome.state]
      exact ⟨first.1, first.2.1, first.2.2.1, first.2.2.2, trivial⟩
  | done edges exposed =>
      by_cases overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
          (SourceCurrentConjunctionTuples.tuples edges)).length
      · have actual := SourceCurrentConjunctionTupleAdmission.run_overflow p h budget nodes before exposed edges read overflow
        simp only [read, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
        simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state]
        exact ⟨first.1, first.2.1, first.2.2.1, first.2.2.2, trivial⟩
      · rw [SourceCurrentConjunctionTupleAdmission.fits_rows p h budget nodes before exposed edges read
          (Nat.le_of_not_gt overflow)]
        have own := SourceCurrentConjunctionRowsWorkerEffects.rows_effects p h nodes before semantic covered available closed
        cases completed : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
        | failed fault after =>
            simp only [completed, SourceCurrentConjunctionRowsWorker.Outcome.state] at own
            simp only [SourceCurrentConjunctionRowsWorker.Outcome.bind,
              SourceCurrentConjunctionRowsWorker.Outcome.state]
            exact ⟨own.1, own.2.1, own.2.2.1, own.2.2.2.1, trivial⟩
        | done requirements after =>
            simp only [completed, SourceCurrentConjunctionRowsWorker.Outcome.state] at own
            cases full : SourceCurrentConjunctionTuples.tuples edges with
            | nil =>
                simp only [SourceCurrentConjunctionRowsWorker.Outcome.bind,
                  SourceCurrentConjunctionRowsWorker.Outcome.state]
                exact ⟨own.1, own.2.1, own.2.2.1, own.2.2.2.1, trivial⟩
            | cons tuple rest =>
                simpa only [completed, SourceCurrentConjunctionRowsWorker.Outcome.bind,
                  SourceCurrentConjunctionRowsWorker.Outcome.state, full] using own

/-- Every actual exploration outcome retains the original weak physical contract. -/
theorem explore_effects (p h budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula)
    (pending : List (List Node)) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (inputs : ∀ nodes ∈ pending, Values before.heap nodes ∧ ClosedValues nodes) :
    let actual := SourceCurrentConjunctionTupleWorker.explore p h budget table pending before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil =>
          simp only [SourceCurrentConjunctionTupleWorker.explore, Outcome.state]
          exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
      | cons nodes rest tail =>
          rw [SourceCurrentConjunctionTupleWorker.explore.eq_def]
          dsimp only
          split
          · exact tail table before semantic covered
              (fun group member => inputs group (List.mem_cons_of_mem _ member))
          · split
            · exact tail table before semantic covered
                (fun group member => inputs group (List.mem_cons_of_mem _ member))
            · have positive := (SourceCurrentConjunctionEmptinessTable.admitted
                SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes
                (Bool.eq_false_iff.mpr (by assumption))).1
              have first := admission_effects p h budget nodes before semantic covered
                (inputs nodes List.mem_cons_self).1 (inputs nodes List.mem_cons_self).2
              cases actual : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before with
              | failed fault after =>
                  simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
                  exact ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1⟩
              | done result middle =>
                  simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first
                  rcases first with ⟨sem, cov, growth, history, returned⟩
                  have oldInputs : ∀ group ∈ rest, Values middle.heap group ∧ ClosedValues group := by
                    intro group member
                    exact ⟨fun value included => ((inputs group (List.mem_cons_of_mem _ member)).1 value included).grows
                      before.heap middle.heap growth history, (inputs group (List.mem_cons_of_mem _ member)).2⟩
                  cases result with
                  | overflow =>
                      have later := smaller 0 positive table rest middle sem cov oldInputs
                      exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1,
                        extends_trans history later.2.2.2⟩
                  | zero =>
                      have later := tail (⟨nodes, []⟩ :: table) middle sem cov oldInputs
                      exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1,
                        extends_trans history later.2.2.2⟩
                  | positive predecessor requirements =>
                      have charge := SourceCurrentConjunctionTupleAdmission.positive_charge p h budget nodes before middle
                        predecessor requirements actual
                      have remaining : ∀ group ∈ requirements.flatten ++ rest,
                          Values middle.heap group ∧ ClosedValues group := by
                        intro group member
                        rcases List.mem_append.mp member with fresh | old
                        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp fresh
                          exact returned row rowIn group groupIn
                        · exact oldInputs group old
                      have later := smaller (budget - (predecessor + 1)) (by omega)
                        (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle sem cov remaining
                      exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1,
                        extends_trans history later.2.2.2⟩

/-- Open starts and all fixed-point outcomes retain the weak heap contract. -/
theorem decision_effects (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    let actual := SourceCurrentConjunctionTupleWorker.decision p h budget query before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  unfold SourceCurrentConjunctionTupleWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes ∧ ClosedValues nodes := by
      intro nodes member
      cases List.mem_singleton.mp member
      constructor
      · intro value included
        cases List.mem_singleton.mp included
        exact available
      · intro value included
        cases List.mem_singleton.mp included
        exact closed
    have first := explore_effects p h budget [] [[query]] before semantic covered inputs
    cases actual : SourceCurrentConjunctionTupleWorker.explore p h budget [] [[query]] before with
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | done table after =>
        rw [actual] at first
        simp only [Outcome.state] at first
        simp only [Outcome.bind]
        split <;> exact first
  · exact ⟨semantic, covered, grows_refl _, extends_refl _⟩

/-- Fourth-memo hits and all actual misses retain the same weak physical effects. -/
theorem call_effects (p h budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo)
    (query : Value Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (before : Physical Symbol FullSyntax.Formula) (semantic : SemanticHeap before.heap)
    (covered : Covered [] before.heap) (available : Available before.heap query) (closed : query.free = []) :
    let actual := SourceCurrentConjunctionTupleWorker.call p h budget memo query before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued := by
  unfold SourceCurrentConjunctionTupleWorker.call
  split
  · exact ⟨semantic, covered, grows_refl _, extends_refl _⟩
  · have first := decision_effects p h budget query before semantic covered available closed
    cases actual : SourceCurrentConjunctionTupleWorker.decision p h budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using first
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using first

end MicroCFTA.SourceCurrentConjunctionTupleWeakEffects
