import MicroCFTA.SourcePruningEnumerationDispatchStability
import MicroCFTA.SourcePruningEnumerationFoldStability
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Stable cached dispatcher and fold observations

The cache adapter has no independent fuel parameter.
An unchanged dispatcher result retains the action and cache reconstruction.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A successful dispatcher observation keeps its complete optional cache at larger bounds. -/
theorem run_ok_stable
    {checkEmpty : Bool} {n N p P h H : Nat}
    {beforeCaller afterCaller : Caller width} {before : Cached}
    {source target : Nat} {queries savedQueries : Queries} {raw : Option Raw} {after : Option Cached}
    (observed : run checkEmpty n p h beforeCaller before source target queries =
      (.ok raw, afterCaller, savedQueries, after))
    (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    run checkEmpty N P H beforeCaller before source target queries =
      (.ok raw, afterCaller, savedQueries, after) := by
  rcases dispatched : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
      beforeCaller before.core source target queries with ⟨outcome, reached, saved⟩
  cases outcome with
  | error fault =>
    simp only [run, dispatched] at observed
    cases observed
  | ok action =>
    have later := SourcePruningEnumerationDispatch.dispatch_ok_stable
      dispatched enoughNative enoughP enoughH
    simpa only [run, dispatched, later] using observed

end MicroCFTA.SourcePruningEnumerationCachedAdapter

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A successful actual fold keeps its raw observation and optional cache at larger bounds. -/
theorem run_ok_stable
    {checkEmpty : Bool} {n N p P h H : Nat} {sources : List Nat}
    {beforeCaller afterCaller : Caller width} {before : Cached}
    {target : Nat} {queries savedQueries : Queries} {raw : Option Raw}
    {outer : Core} {after : Option Cached}
    (observed : run checkEmpty n p h sources beforeCaller before target queries =
      ((.ok raw, afterCaller, savedQueries, outer), after))
    (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    run checkEmpty N P H sources beforeCaller before target queries =
      ((.ok raw, afterCaller, savedQueries, outer), after) := by
  induction sources generalizing beforeCaller before queries with
  | nil => simpa only [run] using observed
  | cons source rest ih =>
    rcases headObserved : SourcePruningEnumerationCachedAdapter.run checkEmpty n p h
        beforeCaller before source target queries with ⟨outcome, reached, saved, headCache⟩
    cases outcome with
    | error fault =>
      simp only [run, headObserved] at observed
      cases observed
    | ok possible =>
      have headLater := SourcePruningEnumerationCachedAdapter.run_ok_stable
        headObserved enoughNative enoughP enoughH
      simp only [run, headObserved] at observed
      simp only [run, headLater]
      cases possible with
      | none => exact observed
      | some rows =>
        cases rows with
        | nil => exact observed
        | cons row tail =>
          cases row with
          | error fault => exact observed
          | ok result =>
            rcases result with ⟨⟨⟩, core⟩
            cases tail with
            | cons second remaining => exact observed
            | nil =>
              cases headCache with
              | none =>
                dsimp only at observed ⊢
                have tailObserved := congrArg Prod.fst observed
                have tailLater := SourcePruningEnumerationFold.run_ok_stable
                  tailObserved enoughNative enoughP enoughH
                have cacheSame : (none : Option Cached) = after := congrArg Prod.snd observed
                rw [tailLater]
                exact Prod.ext rfl cacheSame
              | some recovered => exact ih observed

end MicroCFTA.SourcePruningEnumerationCachedFold
