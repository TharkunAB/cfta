import MicroCFTA.SourcePruningEnumerationSelectedPreparation
import MicroCFTA.SourcePruningEnumerationSharedPreparedContinuations
import MicroCFTA.SourceCurrentRequiredUnionNormalRead

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationPreparationUnionNormal
open EnumerationState InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Selected Mu and Union preparation retains its exact successful or failed native heap. -/
theorem selected_value_unionNormal
    (fuel : Nat) (value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (normal : UnionNormal heap) :
    UnionNormal (SourcePruningEnumerationSelectedValue.run fuel value heap).state
 := by
  cases value with
  | empty | reference | node => exact normal
  | mu entry body depth ordinary =>
      have retained := SourceCurrentRequiredUnionNormal.unfold (.mu entry body depth ordinary) heap normal
      unfold SourcePruningEnumerationSelectedValue.run
      cases actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) heap with
      | pending key after =>
          simpa only [actual, InternedNestedConstruction.Outcome.state,
            MergedSourceComparison.Result.state] using retained
      | done result after =>
          simpa only [actual, InternedNestedConstruction.Outcome.state,
            MergedSourceComparison.Result.state] using retained
  | union entry members depth free =>
      have retained := SourceCurrentRequiredUnionNormalRead.nodeEdges fuel (.union entry members depth free) heap normal
      unfold SourcePruningEnumerationSelectedValue.run
      cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel (.union entry members depth free) heap with
      | done rows after =>
          have afterNormal : UnionNormal after := by
            simpa only [actual, MergedSourceExposure.Result.state] using retained
          simpa only [actual, MergedSourceComparison.Result.state] using
            (SourceCurrentRequiredUnionNormal.node rows after afterNormal)
      | unresolved name after =>
          simpa only [actual, MergedSourceExposure.Result.state,
            MergedSourceComparison.Result.state] using retained
      | pending key after =>
          simpa only [actual, MergedSourceExposure.Result.state,
            MergedSourceComparison.Result.state] using retained
      | exhausted after =>
          simpa only [actual, MergedSourceExposure.Result.state,
            MergedSourceComparison.Result.state] using retained

/-- Every selected preparation retains union normality at its actual endpoint caller. -/
theorem run_endpoint_unionNormal
    (entryFuel nativeFuel uv : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint caller queries
        (SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before)).1.checked.native.machine.heap
 := by
  unfold SourcePruningEnumerationSelectedPreparation.run
  generalize reading : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
    entryFuel uv before.core) = raw
  cases raw with
  | nil => exact normal
  | cons first rest =>
      cases rest with
      | cons another remaining => cases first <;> exact normal
      | nil =>
          cases first with
          | error fault => exact normal
          | ok pair =>
              obtain ⟨⟨target, handle, scs, value⟩, entered⟩ := pair
              exact selected_value_unionNormal nativeFuel value caller.checked.native.machine.heap normal

end MicroCFTA.SourcePruningEnumerationPreparationUnionNormal
