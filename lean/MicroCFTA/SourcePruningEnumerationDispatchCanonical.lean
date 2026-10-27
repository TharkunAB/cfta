import MicroCFTA.SourcePruningEnumerationAssimilationCanonical
import MicroCFTA.SourcePruningEnumerationDispatchShape

namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness EnumerationValidity
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- An actual captured dispatcher singleton preserves canonical suspended tries. -/
theorem dispatch_canonical
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (canonical : Canonical before)
    (selected : dispatch checkEmpty nativeFuel p h beforeCaller before source target queries =
      (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) : Canonical after := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨_different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact canonical
  · exact SourcePruningEnumerationAssimilation.assimilated_canonical before source target
      sourceNode targetNode merged sourceScs targetScs canonical sourceStored targetStored

end MicroCFTA.SourcePruningEnumerationDispatch
