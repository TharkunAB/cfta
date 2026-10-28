import MicroCFTA.SourcePruningEnumerationChildDispatchStability

/-!
# Agreement of actual successful child points

Compare both observations at the same larger bounds.
Every raw result, native caller, query state and cache then agrees.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Fragments.Fragment Symbol × Core))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Two supported successful child returns agree at every returned field. -/
theorem run_some_unique
    {checkEmpty : Bool} {r R n N p P h H k K : Nat}
    {scs : List Suspended} {incoming : Node} {beforeCaller firstCaller secondCaller : Caller width}
    {before firstCache secondCache : Cached} {firstOuter secondOuter : Core}
    {firstWaiting secondWaiting : EnumerationWaitingIndex.Waiting}
    {queries firstQueries secondQueries : Queries} {firstRaw secondRaw : Raw}
    (first : run checkEmpty r n p h k scs incoming beforeCaller before queries =
      ((.ok (some firstRaw), firstCaller, firstQueries, firstOuter, firstWaiting), some firstCache))
    (firstSupported : firstRaw = [] ∨ ∃ fragment returned, firstRaw = [.ok (fragment, returned)])
    (second : run checkEmpty R N P H K scs incoming beforeCaller before queries =
      ((.ok (some secondRaw), secondCaller, secondQueries, secondOuter, secondWaiting), some secondCache))
    (secondSupported : secondRaw = [] ∨ ∃ fragment returned, secondRaw = [.ok (fragment, returned)]) :
    firstRaw = secondRaw ∧ firstCaller = secondCaller ∧ firstQueries = secondQueries ∧
      firstOuter = secondOuter ∧ firstWaiting = secondWaiting ∧ firstCache = secondCache := by
  have one := run_some_stable (R := max r R) (N := max n N) (P := max p P)
    (H := max h H) (K := max k K) first firstSupported
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have two := run_some_stable (R := max r R) (N := max n N) (P := max p P)
    (H := max h H) (K := max k K) second secondSupported
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have pair := Prod.mk.inj (one.symm.trans two)
  have outcome := Prod.mk.inj pair.1
  have caller := Prod.mk.inj outcome.2
  have saved := Prod.mk.inj caller.2
  have outer := Prod.mk.inj saved.2
  exact ⟨Option.some.inj (Except.ok.inj outcome.1), caller.1, saved.1,
    outer.1, outer.2, Option.some.inj pair.2⟩

end MicroCFTA.SourcePruningEnumerationChildDispatch
