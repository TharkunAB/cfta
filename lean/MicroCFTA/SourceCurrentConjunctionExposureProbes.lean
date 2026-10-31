import MicroCFTA.SourceCurrentOpenExposureFields
import MicroCFTA.SourceCurrentConjunctionProbeBirth
import MicroCFTA.SourceCurrentConjunctionRowsWorker

set_option autoImplicit false

/-! Clean probes at every actual conjunction exposure endpoint. -/
namespace MicroCFTA.SourceCurrentConjunctionExposureProbes
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open SourceEqualityRequiredSemanticCache
open InternedFreshOrdinaryProbeHeap (Heap)
open SourceEqualityAnnotationExposure (prepend_state canonical_state)
variable {Symbol Guard : Type}

/-- Every actual collection outcome retains clean probes for completed Mu records. -/
theorem collect_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticReady state)
    (heap : Heap state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) : Heap (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact heap
  | succ fuel ih =>
      cases pending with
      | nil => exact heap
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state semantic heap seen rest restInputs
          | reference => exact heap
          | node entry edges depth free =>
              simpa only [collect, prepend_state] using ih state semantic heap seen rest restInputs
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using
                  ih state semantic heap (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
                  SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
                have retained := SourceCurrentConjunctionProbeBirth.unfold_heap
                  (.mu entry body depth ordinary) state semantic.ready.semantic.1 heap available
                have afterHeap : Heap after := by
                  simpa only [done, Outcome.state] using retained
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact kept.available child (restInputs child member)
                simpa only [collect, ite_eq_right visited, done] using
                  ih after afterSemantic afterHeap (entry.identity :: seen) (result :: rest) nextInputs

/-- Actual direct and closure reads retain clean Mu probes on every outcome. -/
theorem nodeEdges_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (heap : Heap state) (available : Available state value) :
    Heap (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current)
      (currentHeap : Heap current) (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Heap (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collect_heap fuel current currentSemantic currentHeap [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state semantic heap _ available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
      have retained := SourceCurrentConjunctionProbeBirth.unfold_heap
        (.mu entry body depth ordinary) state semantic.ready.semantic.1 heap available
      have afterHeap : Heap after := by
        simpa only [done, Outcome.state] using retained
      have closure := fallback after afterSemantic afterHeap (.mu entry body depth ordinary)
        (kept.available _ available)
      cases result with
      | node => simpa only [nodeEdges, done, Result.state] using afterHeap
      | empty | reference | union | mu => simpa only [nodeEdges, done] using closure

private theorem map_heap {Formula A B : Type}
    (actual : SourceCurrentConjunctionRowsWorker.Outcome Symbol Formula A) (f : A → B) :
    (actual.bind fun value after => .done (f value) after).state.heap = actual.state.heap := by
  cases actual <;> rfl

/-- Ordered operand exposure retains clean Mu probes at its actual returned heap. -/
theorem exposures_heap {Formula : Type}
    [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    (fuel : Nat) (values : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
    (before : SourceCurrentConjunctionRowsAllocation.State Symbol Formula)
    (semantic : SemanticReady before.heap) (costs : InternedFreshOrdinaryCostHeap.Heap before.heap)
    (heap : Heap before.heap) (inputs : Values before.heap values) :
    Heap (SourceCurrentConjunctionRowsWorker.exposures fuel values before).state.heap := by
  induction values generalizing before with
  | nil => exact heap
  | cons value values ih =>
    have first := nodeEdges_heap fuel value before.heap semantic heap (inputs _ List.mem_cons_self)
    have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel value before.heap semantic costs
      (inputs _ List.mem_cons_self)
    cases read : MergedFreshOrdinaryExposure.nodeEdges fuel value before.heap with
    | done edges after =>
      have afterSemantic := checked.semantic
      have afterCosts := checked.costs
      have kept := checked.keeps
      rw [read] at first afterSemantic afterCosts kept
      have later := ih (⟨after, before.equality⟩ : SourceCurrentConjunctionRowsAllocation.State Symbol Formula)
        afterSemantic afterCosts first
        (fun child member => kept.available child (inputs child (List.mem_cons_of_mem _ member)))
      simpa only [SourceCurrentConjunctionRowsWorker.exposures, read, map_heap] using later
    | pending key after =>
      rw [read] at first
      simpa only [SourceCurrentConjunctionRowsWorker.exposures, read,
        SourceCurrentConjunctionRowsWorker.Outcome.state, Result.state] using first
    | unresolved name after =>
      rw [read] at first
      simpa only [SourceCurrentConjunctionRowsWorker.exposures, read,
        SourceCurrentConjunctionRowsWorker.Outcome.state, Result.state] using first
    | exhausted after =>
      rw [read] at first
      simpa only [SourceCurrentConjunctionRowsWorker.exposures, read,
        SourceCurrentConjunctionRowsWorker.Outcome.state, Result.state] using first

end MicroCFTA.SourceCurrentConjunctionExposureProbes
