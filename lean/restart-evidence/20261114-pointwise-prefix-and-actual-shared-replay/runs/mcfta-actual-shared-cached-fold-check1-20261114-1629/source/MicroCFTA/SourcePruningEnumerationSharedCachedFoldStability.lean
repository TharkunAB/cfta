import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
import MicroCFTA.SourcePruningEnumerationSharedDispatchStability

/-!
# Exact outer successful shared fold observations

The shared dispatcher retains its action and native endpoint.
The pure cache adapter uses that same reached heap and raw action result.
Both fold paths retain the raw option, caller, query memo, core and optional cache.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
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

/-- An outer successful raw fold retains every returned field at larger bounds. -/
theorem rawFold_ok_stable
    {checkEmpty : Bool} {n p h N P H : Nat} {sources : List Nat}
    {beforeCaller afterCaller : Caller width} {before after : Core}
    {target : Nat} {queries savedQueries : Queries}
    {result : Option (List (Except EnumerationState.Error
      (Unit × Core)))}
    (observed : rawFold checkEmpty n p h sources beforeCaller before target queries =
      (.ok result, afterCaller, savedQueries, after))
    (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    rawFold checkEmpty N P H sources beforeCaller before target queries =
      (.ok result, afterCaller, savedQueries, after) := by
  induction sources generalizing beforeCaller before queries with
  | nil => simpa only [rawFold] using observed
  | cons source rest ih =>
      rcases selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
          beforeCaller before source target queries with ⟨selection, headCaller, headQueries⟩
      cases selection with
      | error _fault =>
          simp only [rawFold, selected] at observed
          cases observed
      | ok possible =>
          have later := SourcePruningEnumerationSharedDispatch.dispatch_ok_stable
            selected enoughNative enoughP enoughH
          cases possible with
          | none => simpa only [rawFold, selected, later] using observed
          | some action =>
              cases raw : ExceptT.run (action before) with
              | nil => simpa only [rawFold, selected, later, raw] using observed
              | cons first tail =>
                  cases first with
                  | error _fault => simpa only [rawFold, selected, later, raw] using observed
                  | ok pair =>
                      rcases pair with ⟨token, middle⟩
                      cases token
                      cases tail with
                      | nil =>
                          simp only [rawFold, selected, raw] at observed
                          have tailLater := ih (beforeCaller := headCaller) (before := middle)
                            (queries := headQueries) observed
                          simpa only [rawFold, later, raw] using tailLater
                      | cons _second _remaining =>
                          simpa only [rawFold, selected, later, raw] using observed

/-- An outer successful cached dispatch retains the entire optional cache. -/
theorem cachedAdapter_ok_stable
    {checkEmpty : Bool} {n N p P h H : Nat}
    {beforeCaller afterCaller : Caller width} {before : Cached}
    {source target : Nat} {queries savedQueries : Queries} {raw : Option Raw} {after : Option Cached}
    (observed : cachedAdapter checkEmpty n p h beforeCaller before source target queries =
      (.ok raw, afterCaller, savedQueries, after))
    (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    cachedAdapter checkEmpty N P H beforeCaller before source target queries =
      (.ok raw, afterCaller, savedQueries, after) := by
  rcases dispatched : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
      beforeCaller before.core source target queries with ⟨outcome, reached, saved⟩
  cases outcome with
  | error fault =>
    simp only [cachedAdapter, dispatched] at observed
    cases observed
  | ok action =>
    have later := SourcePruningEnumerationSharedDispatch.dispatch_ok_stable
      dispatched enoughNative enoughP enoughH
    simpa only [cachedAdapter, dispatched, later] using observed

/-- An outer successful shared fold retains both its raw endpoint and optional cache. -/
theorem fold_ok_stable
    {checkEmpty : Bool} {n N p P h H : Nat} {sources : List Nat}
    {beforeCaller afterCaller : Caller width} {before : Cached}
    {target : Nat} {queries savedQueries : Queries} {raw : Option Raw}
    {outer : Core} {after : Option Cached}
    (observed : fold checkEmpty n p h sources beforeCaller before target queries =
      ((.ok raw, afterCaller, savedQueries, outer), after))
    (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    fold checkEmpty N P H sources beforeCaller before target queries =
      ((.ok raw, afterCaller, savedQueries, outer), after) := by
  induction sources generalizing beforeCaller before queries with
  | nil => simpa only [fold] using observed
  | cons source rest ih =>
    rcases headObserved : cachedAdapter checkEmpty n p h
        beforeCaller before source target queries with ⟨outcome, reached, saved, headCache⟩
    cases outcome with
    | error fault =>
      simp only [fold, headObserved] at observed
      cases observed
    | ok possible =>
      have headLater := cachedAdapter_ok_stable
        headObserved enoughNative enoughP enoughH
      simp only [fold, headObserved] at observed
      simp only [fold, headLater]
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
                have tailLater := rawFold_ok_stable
                  tailObserved enoughNative enoughP enoughH
                have cacheSame : (none : Option Cached) = after := congrArg Prod.snd observed
                rw [tailLater]
                exact Prod.ext rfl cacheSame
              | some recovered => exact ih observed

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal

#print axioms MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.rawFold_ok_stable
#print axioms MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.cachedAdapter_ok_stable
#print axioms MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.fold_ok_stable
