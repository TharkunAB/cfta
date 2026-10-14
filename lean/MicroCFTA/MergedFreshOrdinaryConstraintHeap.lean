import MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap
import MicroCFTA.MergedFreshOrdinaryColdEffects

/-!
# Constraint invariants through actual repaired cold exposure

The cold reader exposes stored ordinary edges and unfolds recursive values.
Neither path introduces a constraint outside the checked source cache.
-/
namespace MicroCFTA.MergedFreshOrdinaryConstraintHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedColdReaderClosedInputs (ClosedValues)
open InternedFreshOrdinaryConstraintHeap (Heap)
open MergedFreshOrdinaryExposure

/-- Every bounded actual closure walk retains the source edge-constraint invariant. -/
theorem collect_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : Heap property state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (closed : ClosedValues pending) : Heap property (collect fuel state seen pending).state := by
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
          | reference name => exact heap
          | node entry edges depth free =>
              have next := ih state semantic covered heap seen rest restInputs restClosed
              cases found : collect fuel state seen rest <;> simpa only [collect, found, MergedSourceExposure.Result.prepend,
                MergedSourceExposure.Result.state] using next
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered heap seen rest restInputs restClosed
              · have next := ih state semantic covered heap (entry.identity :: seen) (members ++ rest)
                  (fun child member => (List.mem_append.mp member).elim (available.children child) (restInputs child))
                  (fun child member => (List.mem_append.mp member).elim
                    (MergedColdReaderClosed.union_members_closed state semantic.1.normal.facts entry members depth free available valueClosed child)
                    (restClosed child))
                simpa only [collect, ite_eq_right visited] using next
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered heap seen rest restInputs restClosed
              · obtain ⟨result, after, done, context, depthHeap, finalCovered, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have afterHeap : Heap property after := by
                  simpa only [done, InternedNestedConstruction.Outcome.state] using
                    InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property _ state semantic.1.normal.facts heap available
                have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
                  state semantic.1 available valueClosed result after done
                have next := ih after ⟨context, depthHeap⟩ finalCovered afterHeap (entry.identity :: seen) (result :: rest)
                  (fun child member => (List.mem_cons.mp member).elim
                    (fun same => same ▸ resultAvailable) (fun later => (restInputs child later).grows state after growth history))
                  (fun child member => (List.mem_cons.mp member).elim (fun same => same ▸ resultClosed) (restClosed child))
                simpa only [collect, ite_eq_right visited, done] using next

/-- Actual direct and fallback exposure retain all normalized source constraints. -/
theorem nodeEdges_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : Heap property state)
    (available : Available state value) (closed : value.free = []) : Heap property (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (currentHeap : Heap property current) (root : Value Symbol Guard)
      (rootAvailable : Available current root) (rootClosed : root.free = []) :
      Heap property (collect fuel current [] [root]).canonical.state := by
    have next := collect_heap property fuel current currentSemantic currentCovered currentHeap [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootClosed)
    cases found : collect fuel current [] [root] <;>
      simpa only [found, MergedSourceExposure.Result.canonical, MergedSourceExposure.Result.state] using next
  cases value with
  | empty | reference | node => exact heap
  | union entry members depth free => exact fallback state semantic covered heap _ available closed
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, context, depthHeap, finalCovered, _, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have afterHeap : Heap property after := by
        simpa only [done, InternedNestedConstruction.Outcome.state] using
          InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property _ state semantic.1.normal.facts heap available
      have next := fallback after ⟨context, depthHeap⟩ finalCovered afterHeap _ (available.grows state after growth history) closed
      cases result with
      | node => simpa only [nodeEdges, done, MergedSourceExposure.Result.state] using afterHeap
      | empty | reference | union | mu => simpa only [nodeEdges, done] using next

end MicroCFTA.MergedFreshOrdinaryConstraintHeap
