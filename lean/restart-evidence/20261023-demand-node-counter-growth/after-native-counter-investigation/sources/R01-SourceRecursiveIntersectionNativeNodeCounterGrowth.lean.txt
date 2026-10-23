import MicroCFTA.InternedFreshOrdinaryStoredNodeCounterGrowth
import MicroCFTA.SourceRecursiveIntersectionNativePrefixCoverage

namespace MicroCFTA.SourceRecursiveIntersectionNativeNodeCounterGrowth
open InternedConstructorTemplates
open SourceRecursiveIntersectionCode (Code)
variable {Symbol Guard A : Type} {width : Nat}

/-- One native step retains or increases its actual constructor node counter. -/
theorem step_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (code : Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    state.machine.heap.nodes.next ≤
      (SourceRecursiveIntersectionNative.step emptyGuard conjoin code state).state.machine.heap.nodes.next := by
  cases code with
  | pure | fail | enter | read | finishNode | finishEdge => exact Nat.le_refl _
  | work job next =>
      simp only [SourceRecursiveIntersectionNative.step,
        SourceRecursiveIntersectionNative.Outcome.state, SourceRecursiveIntersectionThunks.advance]
      rw [(SourceCurrentAllocatedFiniteOrdinaryReservations.run_next job state.machine.heap).1]
      exact Nat.le_add_right _ _
  | optionalBinder key body next =>
      have growth : state.machine.heap.nodes.next ≤
          (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap).state.nodes.next := by
        exact InternedFreshOrdinaryStoredNodeCounterGrowth.maybeMu_mono key body state.machine.heap
      cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
      | done value after =>
          simpa only [SourceRecursiveIntersectionNative.step, constructed,
            SourceRecursiveIntersectionNative.Outcome.state, SourceRecursiveIntersectionThunks.advance,
            InternedNestedConstruction.Outcome.state] using growth
      | pending pending after =>
          simpa only [SourceRecursiveIntersectionNative.step, constructed,
            SourceRecursiveIntersectionNative.Outcome.state, SourceRecursiveIntersectionThunks.advance,
            InternedNestedConstruction.Outcome.state] using growth
  | node request next =>
      rw [SourceRecursiveIntersectionNative.node_step_machine]
      exact Nat.le_refl _
  | edge request next =>
      rw [SourceRecursiveIntersectionNative.edge_step_machine]
      exact Nat.le_refl _

/-- Every finite native outcome retains or increases its input constructor node counter. -/
theorem execute_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    state.machine.heap.nodes.next ≤
      (SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel code state).state.machine.heap.nodes.next := by
  induction fuel generalizing code state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      have first : state.machine.heap.nodes.next ≤
          (SourceRecursiveIntersectionNative.step emptyGuard conjoin code state).state.machine.heap.nodes.next := by
        exact step_mono emptyGuard conjoin code state
      cases observed : SourceRecursiveIntersectionNative.step emptyGuard conjoin code state with
      | yielded next after =>
          simp only [observed, SourceRecursiveIntersectionNative.Outcome.state] at first
          simpa only [SourceRecursiveIntersectionNative.execute, observed] using
            Nat.le_trans first (ih next after)
      | done value after =>
          simpa only [SourceRecursiveIntersectionNative.execute, observed,
            SourceRecursiveIntersectionNative.Outcome.state] using first
      | failed failure after =>
          simpa only [SourceRecursiveIntersectionNative.execute, observed,
            SourceRecursiveIntersectionNative.Outcome.state] using first
      | blocked reason next after =>
          simpa only [SourceRecursiveIntersectionNative.execute, observed,
            SourceRecursiveIntersectionNative.Outcome.state] using first

/-- Resuming an actual outcome retains or increases its current constructor node counter. -/
theorem resume_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    outcome.state.machine.heap.nodes.next ≤
      (SourceRecursiveIntersectionNative.resume emptyGuard conjoin fuel outcome).state.machine.heap.nodes.next := by
  cases outcome with
  | yielded code state => exact execute_mono emptyGuard conjoin fuel code state
  | done | failed | blocked => exact Nat.le_refl _

end MicroCFTA.SourceRecursiveIntersectionNativeNodeCounterGrowth
