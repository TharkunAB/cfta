import MicroCFTA.SourcePruningEnumerationKeyAncestry
import MicroCFTA.SourcePruningEnumerationDispatchShape

/-!
# Historical key shapes at the actual raw dispatch singleton

The actual returned core is unchanged or is the exact assimilation update.
Both cases retain the original whole-shape carrier.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- The same actual successful raw action preserves both ancestry fields' key-shape carrier. -/
theorem dispatch_key_ancestry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    {carrier : List (List (List (List Nat)))}
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (bounded : KeyAncestry carrier before)
    (selected : dispatch checkEmpty nativeFuel p h beforeCaller before source target queries =
      (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    KeyAncestry carrier after := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨_different, _sourceNode, _targetNode, merged, sourceScs, targetScs, _sourceStored, _targetStored, rfl⟩
  · exact bounded
  · exact bounded.assimilated target source (.unenumerated merged (sourceScs ++ targetScs))

end MicroCFTA.SourcePruningEnumerationDispatch
