import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion

namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}

/-- Native heap growth preserves validity of the same captured cache. -/
theorem cacheValid_keeps (caller nextCaller : Caller width) (before : Cached)
    (valid : CacheValid caller before)
    (kept : SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap
      nextCaller.checked.native.machine.heap) :
    CacheValid nextCaller before := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := valid
  refine ⟨roots, paths, storage, ?_, counts, ?_⟩
  · exact SourcePruningEnumerationObservation.realized_preserved _ _ before.core before.core
      realized (EnumerationCompressionFrame.Frame.refl _) kept
  · exact SourcePruningEnumerationNativeGrowth.flags _ _ kept before flags

/-- An actual caller postcondition preserves validity of the captured cache. -/
theorem cacheValid_post [DecidableEq (EdgeKey Symbol Constraint)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {next : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {final : EndpointMemoGateTrace.Memos}
    (caller nextCaller : Caller width) (before : Cached) (valid : CacheValid caller before)
    (post : SourceCurrentAllocatedPartialInvariant.Post formulas solver next caller nextCaller final) :
    CacheValid nextCaller before :=
  cacheValid_keeps caller nextCaller before valid post.effects.keeps

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
