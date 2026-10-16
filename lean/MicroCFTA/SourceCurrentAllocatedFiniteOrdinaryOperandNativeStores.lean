import MicroCFTA.SourceCurrentAllocatedMergeOperand
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputStored

/-!
# Native certificates through the same checked operand

Projection and Merge retain both complete native result tables.
Their existing receipt therefore retains structural and output certificates.
The actual Merge call also retains its completed profile table.
These facts require no constructor capacity or future query premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores
open Cache InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {path : List Int} {values : List (Value Symbol Guard)}
    {before after : SourceEqualityNativeDemand.State width}
    {memo saved : SourceCurrentAllocatedMergeGraph.Memo} {output : Value Symbol Guard}
    {memos final : EndpointMemoGateTrace.Memos}

/-- The exact operand receipt retains both native certificate families and idle status. -/
theorem native
    (actual : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo output after saved memos final)
    (stored : NativeStored before.native) (profiles : OutputStored before.native) (idle : Idle before.native) :
    NativeStored after.native ∧ OutputStored after.native ∧ Idle after.native := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa only [actual.nodes] using stored.nodes
  · simpa only [actual.edges] using stored.edges
  · simpa only [actual.nodes] using profiles.nodes
  · simpa only [actual.edges] using profiles.edges
  · simpa only [actual.nodes] using idle.1
  · simpa only [actual.edges] using idle.2

/-- The same actual projection and Merge retain all three certificate families. -/
theorem receipt
    (actual : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo output after saved memos final)
    (physical : PhysicalStored before.native.machine.heap memo) (merged : Profiles memo)
    (stored : NativeStored before.native) (profiles : OutputStored before.native) (idle : Idle before.native) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧ Idle after.native := by
  have nativeAfter := native actual stored profiles idle
  obtain ⟨projected, middle, current, projection, merge⟩ := actual.actual
  have mergedAfter : Profiles saved := by
    cases merge.actual with
    | done call =>
        have produced := SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer.call_profile call.graph
          projection.ready.semantic projection.ready.costs
          (physical.grows projection.effects.keeps) merged projection.available
        exact produced.2.2.1
  exact ⟨mergedAfter, nativeAfter⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores
