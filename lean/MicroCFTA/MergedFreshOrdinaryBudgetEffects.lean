import MicroCFTA.MergedFreshOrdinaryColdEffects
import MicroCFTA.InternedGuardedBudgetStoredExecution

/-!
# Budget probe heaps through actual repaired cold reads

Each source unfolding preserves the budget-language probe invariant.
The actual cold worklist therefore retains this invariant through every
bounded read, including exhausted bounds. Earlier decoded heaps stay separate.
-/
namespace MicroCFTA.MergedFreshOrdinaryBudgetEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedSourceExposure (Result)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedGuardedBudgetProbeHeap (Heap)
open MergedFreshOrdinaryExposure

/-- Prepending constructor edges leaves the actual result cache unchanged. -/
theorem prepend_state (result : Result Symbol Guard) (edges : List (EdgeValue Symbol Guard)) :
    (result.prepend edges).state = result.state := by cases result <;> rfl

/-- Canonical edge ordering leaves the actual result cache unchanged. -/
theorem canonical_state (result : Result Symbol Guard) : result.canonical.state = result.state := by cases result <;> rfl

/-- Every bounded actual cold worklist retains the derived budget probe heap. -/
theorem collect_heap [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : Heap state) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending) (closed : ClosedValues pending) :
    Heap (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact heap
  | succ fuel ih =>
      cases pending with
      | nil => exact heap
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have valueClosed := closed value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state semantic covered heap seen rest restInputs restClosed
          | reference => exact heap
          | node entry edges depth free =>
              simpa only [collect, prepend_state] using ih state semantic covered heap seen rest restInputs restClosed
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered heap seen rest restInputs restClosed
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                have nextClosed : ClosedValues (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact MergedColdReaderClosed.union_members_closed state semantic.1.normal.facts entry members depth free available valueClosed child first
                  · exact restClosed child later
                simpa only [collect, ite_eq_right visited] using
                  ih state semantic covered heap (entry.identity :: seen) (members ++ rest) nextInputs nextClosed
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered heap seen rest restInputs restClosed
              · have retained := (InternedGuardedBudgetStoredExecution.unfold_heaps (.mu entry body depth ordinary) state semantic.1 heap semantic.2 available).1
                obtain ⟨result, after, done, context, cached, finalCovered, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have afterHeap : Heap after := by simpa only [done, InternedNestedConstruction.Outcome.state] using retained
                have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
                  state semantic.1 available valueClosed result after done
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact (restInputs child member).grows state after growth history
                have nextClosed : ClosedValues (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultClosed
                  · exact restClosed child member
                simpa only [collect, ite_eq_right visited, done] using ih after ⟨context, cached⟩ finalCovered afterHeap
                  (entry.identity :: seen) (result :: rest) nextInputs nextClosed

/-- Both direct and closure cold-reader paths preserve the budget probe-language heap. -/
theorem nodeEdges_heap [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : Heap state) (available : Available state value) (closed : value.free = []) :
    Heap (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (currentHeap : Heap current) (root : Value Symbol Guard)
      (rootAvailable : Available current root) (rootClosed : root.free = []) :
      Heap (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collect_heap fuel current currentSemantic currentCovered currentHeap [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootClosed)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state semantic covered heap _ available closed
  | mu entry body depth ordinary =>
      have retained := (InternedGuardedBudgetStoredExecution.unfold_heaps (.mu entry body depth ordinary) state semantic.1 heap semantic.2 available).1
      obtain ⟨result, after, done, context, cached, finalCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have afterHeap : Heap after := by simpa only [done, InternedNestedConstruction.Outcome.state] using retained
      have rootAvailable := available.grows state after growth history
      have closure := fallback after ⟨context, cached⟩ finalCovered afterHeap _ rootAvailable closed
      cases result with
      | node => simpa only [nodeEdges, done, Result.state] using afterHeap
      | empty | reference | union | mu => simpa only [nodeEdges, done] using closure

end MicroCFTA.MergedFreshOrdinaryBudgetEffects
