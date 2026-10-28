import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.MergedFreshOrdinaryColdBudget

/-!
# A fixed Mu-body degree bound through actual selected preparation

The original bound covers every complete Mu record in the input heap.
Actual closed unfolding derives lower-degree allocation from its source plan.
Union exposure keeps the bound, and final row construction adds no Mu.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache
open InternedMuDepthInventory (Bounded bounded_after)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual completed selected operation retains the same original Mu-body degree ceiling. -/
theorem run_mu_bounded
    (limit fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (bounded : Bounded before limit)
    (observed : run fuel value before = .done result after) :
    Bounded after limit := by
  cases value with
  | empty | reference | node =>
      cases observed
      exact bounded
  | mu entry body depth ordinary =>
      have lower := InternedStoredPlanBinderDepthProgress.unfold_new_lower
        (.mu entry body depth ordinary) before semantic.ready.semantic.1
        semantic.ready.semantic.2 semantic.ready.depth available closed
      cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before with
      | done produced middle =>
          have actualLower : InternedStoredPlanBinderDepthProgress.Lower before
              (InternedStoredPlanBinderDepth.valueDepth body) middle := by
            simpa only [unfolded, InternedNestedConstruction.Outcome.state,
              InternedStoredPlanBinderDepth.bodyDepth] using lower
          have middleBounded := bounded_after before middle limit
            (InternedStoredPlanBinderDepth.valueDepth body) bounded
            (bounded entry.key entry body depth ordinary (available.resident entry rfl)) actualLower
          have afterSame : middle = after :=
            (MergedSourceComparison.Result.done.inj (by
              simpa only [run, unfolded] using observed)).2
          simpa only [afterSame] using middleBounded
      | pending key middle =>
          simp only [run, unfolded] at observed
          cases observed
  | union entry members depth free =>
      cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | done rows middle =>
          have readBounds := MergedFreshOrdinaryColdBudget.nodeEdges_progress fuel limit
            (.union entry members depth free) before semantic.ready.semantic
            semantic.ready.covered semantic.ready.depth bounded available closed rows middle exposed
          have rebuiltBounded : Bounded (InternedConstructorTemplates.run (makeNode rows) middle).2 limit := by
            intro key actual body depth ordinary present
            exact readBounds.2.1 key actual body depth ordinary
              (InternedShallowHeap.makeNode_noNewMu rows middle key actual body depth ordinary present)
          have afterSame : (InternedConstructorTemplates.run (makeNode rows) middle).2 = after :=
            (MergedSourceComparison.Result.done.inj (by
              simpa only [run, exposed] using observed)).2
          simpa only [afterSame] using rebuiltBounded
      | unresolved name middle | pending key middle | exhausted middle =>
          simp only [run, exposed] at observed
          cases observed

end MicroCFTA.SourcePruningEnumerationSelectedValue
