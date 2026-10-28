import MicroCFTA.SourceEqualityExposureCosts

/-!
# Physical annotations through bounded exposure of open values

Each actual unfolding retains the original edge annotation predicate.
Available worklist values supply the next unfolding scope. The proof
retains the predicate at every bounded outcome and needs no closed input.
-/
namespace MicroCFTA.SourceCurrentOpenExposureFields
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationHeap (Heap)
open SourceEqualityAnnotationExposure (prepend_state canonical_state)

/-- Bounded collection retains physical edge annotations with unrelated open inputs. -/
theorem collect_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticReady state)
    (heap : Heap property state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) : Heap property (collect fuel state seen pending).state := by
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
                have retained := InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property
                  (.mu entry body depth ordinary) state semantic.ready.semantic.1.normal.facts heap available
                have afterHeap : Heap property after := by
                  simpa only [InternedFreshOrdinaryConstraintHeap.Heap, Heap, done, Outcome.state] using retained
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact kept.available child (restInputs child member)
                simpa only [collect, ite_eq_right visited, done] using
                  ih after afterSemantic afterHeap (entry.identity :: seen) (result :: rest) nextInputs

/-- Actual direct and closure reads retain physical annotations without whole-value closedness. -/
theorem nodeEdges_heap (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (heap : Heap property state) (available : Available state value) :
    Heap property (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current)
      (currentHeap : Heap property current) (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Heap property (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collect_heap property fuel current currentSemantic currentHeap [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state semantic heap _ available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
      have retained := InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property
        (.mu entry body depth ordinary) state semantic.ready.semantic.1.normal.facts heap available
      have afterHeap : Heap property after := by
        simpa only [InternedFreshOrdinaryConstraintHeap.Heap, Heap, done, Outcome.state] using retained
      have closure := fallback after afterSemantic afterHeap (.mu entry body depth ordinary)
        (kept.available _ available)
      cases result with
      | node => simpa only [nodeEdges, done, Result.state] using afterHeap
      | empty | reference | union | mu => simpa only [nodeEdges, done] using closure

end MicroCFTA.SourceCurrentOpenExposureFields
