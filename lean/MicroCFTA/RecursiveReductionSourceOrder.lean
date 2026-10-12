import MicroCFTA.RecursiveReductionBarrier
import MicroCFTA.GuardStructuralOrder
import MicroCFTA.SourceConstraintConjunction
import MicroCFTA.SourceFormula

/-!
# Finite leaf reduction under the exact source guard order

This instance removes the comparator premises from the three-leaf reduction
theorem. The source comparator also decides structural guard equality.
-/
namespace MicroCFTA.RecursiveReductionSourceOrder
open SourceGuards FullSyntax RecursiveReductionBarrier

/-- The proved source comparator decides equality of every current guard constructor. -/
instance guardDecidableEq : DecidableEq (Guard Formula) := fun first second =>
  if equal : GuardStructuralOrder.compareGuard first second = .eq then
    .isTrue ((GuardStructuralOrder.guard_eq first second).mp equal)
  else .isFalse (fun same => equal ((GuardStructuralOrder.guard_eq first second).mpr same))

/-- The actual source order produces one identical residual at all three leaf positions. -/
theorem round_normalizes (a b c : Guard Formula) :
    LeafTriple.round GuardStructuralOrder.le (a, b, c) =
      let common := GuardConjunction.normalize GuardStructuralOrder.le (.and [a, b, c])
      (common, common, common) :=
  LeafTriple.round_normalizes GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm a b c

/-- The finite leaf representation is an actual structural fixed point after one round. -/
theorem round_fixed (state : Guard Formula × Guard Formula × Guard Formula) :
    LeafTriple.round GuardStructuralOrder.le (LeafTriple.round GuardStructuralOrder.le state) =
      LeafTriple.round GuardStructuralOrder.le state :=
  LeafTriple.round_fixed GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm state

/-- The source-order leaf guard loop terminates after at most two passes for every input triple. -/
theorem terminates_two (state : Guard Formula × Guard Formula × Guard Formula) :
    LeafTriple.run GuardStructuralOrder.le 2 state = some (LeafTriple.round GuardStructuralOrder.le state) :=
  LeafTriple.terminates_two GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm state

/-- The shared canonical residual accepts exactly the terms confirmed by all three original guards. -/
theorem common_exact (solver : Entailment Formula) (a b c : Guard Formula)
    (term : Language.Term (SourceObservations.Label Formula)) :
    SourceBooleanEntry.evaluateGuard SourceFormula.operations solver
      (GuardConjunction.normalize GuardStructuralOrder.le (.and [a, b, c])) term = .yes ↔
    SourceBooleanEntry.evaluateGuard SourceFormula.operations solver a term = .yes ∧
    SourceBooleanEntry.evaluateGuard SourceFormula.operations solver b term = .yes ∧
    SourceBooleanEntry.evaluateGuard SourceFormula.operations solver c term = .yes := by
  unfold SourceBooleanEntry.evaluateGuard SourceBooleanEntry.evaluateGuardWithSame
  rw [SourceBooleanEntry.normalize_evaluate]
  have exact := SourceBooleanEntry.conjunction_yes SourceFormula.operations solver
    (SourceObservations.observe term) (SourceObservations.sameTerm SourceFormula.operations term) [a, b, c]
  simpa [SourceBooleanEntry.evaluateGuardWithSame] using exact

end MicroCFTA.RecursiveReductionSourceOrder
