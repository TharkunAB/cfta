import MicroCFTA.SourceEqualityTargetOperand

/-!
# Source targets with interleaved operand demands

The source takes the first path as seed and folds the remaining paths
from right to left. A recursive fold demands its left operand before its
tail. The base demands the seed. Every native step uses the returned state.
-/
namespace MicroCFTA.SourceEqualityDemandTarget
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityTargetOperand

/-- The first-seeded source right fold interleaves actual captured-forest operands and native requests. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) : List (List Int) →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Value Symbol Guard →
        SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | nil (seedDemand : Operand clear top seed values before result after) :
      Fold emptyGuard conjoin clear top values seed [] before result after
  | cons (operand : Operand clear top path values before value middle)
      (rest : Fold emptyGuard conjoin clear top values seed paths middle tail later)
      (step : Step emptyGuard conjoin value tail later result after) :
      Fold emptyGuard conjoin clear top values seed (path :: paths) before result after

/-- The empty target list returns EmptyNode; a nonempty list uses its first path as the deferred seed. -/
inductive Target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) : List (List Int) →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Value Symbol Guard →
        SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | nil : Target emptyGuard conjoin clear top values [] state .empty state
  | cons (fold : Fold emptyGuard conjoin clear top values seed paths before result after) :
      Target emptyGuard conjoin clear top values (seed :: paths) before result after

/-- Every actual demanded target fold retains warm validity, captured scope, and closed target availability. -/
theorem Fold.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] := by
  induction trace with
  | nil seedDemand =>
      have checked := seedDemand.effects ready available closed
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | @cons path before value middle paths tail later result after operand rest step ih =>
      have first := operand.effects ready available closed
      have remaining := ih first.1 (fun value member => first.2.1.available value (available value member))
      have checked := step.verified remaining.1 (remaining.2.1.available value first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 (fun _ _ => true) (fun _ _ _ => rfl)
      exact ⟨checked.1, first.2.1.trans (remaining.2.1.trans checked.2.1), checked.2.2.1, checked.2.2.2.1⟩

/-- Every completed source target retains its actual full native state and physical closed result. -/
theorem Target.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] := by
  cases trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons fold => exact fold.effects ready available closed

end MicroCFTA.SourceEqualityDemandTarget
