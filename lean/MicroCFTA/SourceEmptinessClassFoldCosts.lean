import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.SourceEqualityNativeScopedCosts
import MicroCFTA.SourceEmptinessClassFold

/-!
# Cost heaps through actual class folds

Projection retains costs for open operands. The closed-forest fold uses
its existing readiness proof at each actual native call. Each recursive
call receives the heap returned by the preceding operation.
-/
namespace MicroCFTA.SourceEmptinessClassFoldCosts
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNativeScoped SourceEmptinessProjection SourceEmptinessClassFold
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- An actual plain operand retains costs without requiring a closed original forest. -/
theorem operand_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (costs : CostHeap before.machine.heap) :
    CostHeap after.machine.heap := by
  cases trace with
  | force projection =>
      exact (SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available).2.2.1

/-- The actual closed-forest fold retains costs through projection, tail evaluation, and intersection. -/
theorem fold_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  induction trace with
  | one operand => exact operand_costs operand ready available costs
  | cons operand rest native ih =>
      have first := operand.effects ready available closed
      have firstCosts := operand_costs operand ready available costs
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have remaining := rest.effects first.1 tailInputs closed
      have tailCosts := ih first.1 tailInputs firstCosts
      exact native.cost_heap remaining.1 tailCosts (remaining.2.1.available _ first.2.2.1) remaining.2.2.1

/-- The actual seeded rotation and its empty-list fallback retain costs. -/
theorem seeded_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  cases paths with
  | nil => obtain ⟨_, rfl⟩ := trace; exact costs
  | cons => exact fold_costs trace ready available closed costs

end MicroCFTA.SourceEmptinessClassFoldCosts
