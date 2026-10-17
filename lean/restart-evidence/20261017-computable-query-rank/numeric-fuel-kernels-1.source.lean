import MicroCFTA.IntersectNumericFuel

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.NumericFuelResetKernel
open Language Binding BinderLanguage IntersectSchedule

/-- A literal ready reset and its new closed-root family have the same independently produced result. -/
theorem reset_same_result [DecidableEq Symbol] (view : View Symbol) (inputs : FiniteInput view)
    (freeCorrect : FreeCorrect view) (bounds : InputBounds view inputs)
    (rank : ClosedRoots view inputs → Call Symbol → Nat)
    (rootDecrease : ∀ (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol),
      bounds.size nextRoots.left + bounds.size nextRoots.right < bounds.size roots.left + bounds.size roots.right →
      WorkReady bounds roots parent → WorkReady bounds nextRoots child → rank nextRoots child < rank roots parent)
    (localDecrease : ∀ (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol),
      bounds.size nextRoots.left + bounds.size nextRoots.right = bounds.size roots.left + bounds.size roots.right →
      WorkReady bounds roots parent → WorkReady bounds nextRoots child → LocalStep view bounds.pairs child parent →
      rank nextRoots child < rank roots parent)
    (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input)
    (ready : NodeReady roots domain left right) (nonempty : ¬(left = .empty ∨ right = .empty))
    (reset : (closed view left && closed view right && !domain.free.isEmpty) = true) :
    ∃ nextRoots : ClosedRoots view inputs,
      nextRoots.left = left ∧ nextRoots.right = right ∧
      rank nextRoots (.node {} left right) < rank roots (.node domain left right) ∧
      ∃ result,
        (∀ fuel, rank roots (.node domain left right) + 1 ≤ fuel → run view fuel domain left right = .ok result) ∧
        ∀ fuel, rank nextRoots (.node {} left right) + 1 ≤ fuel → run view fuel {} left right = .ok result := by
  have leftValid := input_reach_valid view inputs roots.left left roots.left_valid ready.left_reach
  have rightValid := input_reach_valid view inputs roots.right right roots.right_valid ready.right_reach
  have isClosed : closed view left = true ∧ closed view right = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at reset
    exact reset.1
  let nextRoots : ClosedRoots view inputs := ⟨left, right, leftValid, rightValid, isClosed.1, isClosed.2⟩
  have nextReady := roots_ready view inputs nextRoots
  have smaller := rootDecrease roots nextRoots _ _ (reset_decreases bounds roots domain left right ready reset) ready nextReady
  obtain ⟨parentResult, parentDone⟩ := call_numeric view inputs freeCorrect bounds rank rootDecrease localDecrease roots _ ready
  obtain ⟨childResult, childDone⟩ := call_numeric view inputs freeCorrect bounds rank rootDecrease localDecrease nextRoots _ nextReady
  let fuel := rank roots (.node domain left right) + rank nextRoots (.node {} left right) + 2
  have step : run view (fuel + 1) domain left right = run view fuel {} left right := by
    rw [run.eq_def]
    simp only [nonempty, ite_false, reset, ite_true]
  have same : parentResult = childResult := Except.ok.inj
    ((parentDone (fuel + 1) (by dsimp only [fuel]; omega)).symm.trans
      (step.trans (childDone fuel (by dsimp only [fuel]; omega))))
  subst parentResult
  exact ⟨nextRoots, rfl, rfl, smaller, childResult, parentDone, childDone⟩

end MicroCFTA.NumericFuelResetKernel

#print axioms MicroCFTA.NumericFuelResetKernel.reset_same_result
#check @MicroCFTA.NumericFuelResetKernel.reset_same_result
