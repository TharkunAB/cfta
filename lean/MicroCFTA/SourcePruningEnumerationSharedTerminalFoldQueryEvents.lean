import MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal

/-!
# Query events through actual terminal folds

The fold keeps the complete original observation and its optional cache.
Events from a raw tail remain present when the cache is unavailable.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedTerminalFoldQueryEvents
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedDispatchQueryEvents (Event)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
local notation "Fault" => SourceEqualityNativeDemand.Outcome width Node ⊕ SourcePruningEnumerationSharedEnabledEmpty.Outcome width
local notation "Head" => Except Fault (Option Raw) × Caller width × Queries
local notation "RawResult" => Except Fault (Option Raw) × Caller width × Queries × Core
local notation "Adapter" => Except Fault (Option Raw) × Caller width × Queries × Option Cached
local notation "FoldResult" => RawResult × Option Cached
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private noncomputable def rawHeadObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) : Head × List (Event width) :=
  let observed := SourcePruningEnumerationSharedDispatchQueryEvents.observe checkEmpty nativeFuel p h caller before source target queries
  (match observed.1 with
    | (.error fault, reached, saved) => (.error fault, reached, saved)
    | (.ok none, reached, saved) => (.ok none, reached, saved)
    | (.ok (some action), reached, saved) => (.ok (some (ExceptT.run (action before))), reached, saved), observed.2)

/-- Retain the actual raw fold and all query events in execution order. -/
noncomputable def rawFoldObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Core) (target : Nat) (queries : Queries) : RawResult × List (Event width) :=
  match sources with
  | [] => ((.ok (some [.ok ((), before)]), caller, queries, before), [])
  | source :: rest =>
      let head := rawHeadObserved checkEmpty nativeFuel p h caller before source target queries
      match head.1 with
      | (.error fault, reached, saved) => ((.error fault, reached, saved, before), head.2)
      | (.ok none, reached, saved) => ((.ok none, reached, saved, before), head.2)
      | (.ok (some raw), reached, saved) =>
          match raw with
          | [.ok ((), after)] =>
              let tail := rawFoldObserved checkEmpty nativeFuel p h rest reached after target saved
              (tail.1, head.2 ++ tail.2)
          | other => ((.ok (some other), reached, saved, before), head.2)

/-- Attach the existing cache adapter to the same executed raw head. -/
noncomputable def cachedAdapterObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) : Adapter × List (Event width) :=
  let head := rawHeadObserved checkEmpty nativeFuel p h caller before.core source target queries
  (match head.1 with
    | (.error fault, reached, saved) => (.error fault, reached, saved, none)
    | (.ok none, reached, saved) => (.ok none, reached, saved, none)
    | (.ok (some raw), reached, saved) => (.ok (some raw), reached, saved,
        SourcePruningEnumerationCachedAdapter.adapt reached.checked.native.machine.heap before source target raw), head.2)

/-- Retain cached and raw continuation events at their actual reached endpoints. -/
noncomputable def foldObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries) : FoldResult × List (Event width) :=
  match sources with
  | [] => (((.ok (some [.ok ((), before.core)]), caller, queries, before.core), some before), [])
  | source :: rest =>
      let head := cachedAdapterObserved checkEmpty nativeFuel p h caller before source target queries
      match head.1 with
      | (.error fault, reached, saved, _) => (((.error fault, reached, saved, before.core), none), head.2)
      | (.ok none, reached, saved, _) => (((.ok none, reached, saved, before.core), none), head.2)
      | (.ok (some raw), reached, saved, cache) =>
          match raw with
          | [.ok ((), core)] =>
              match cache with
              | none =>
                  let tail := rawFoldObserved checkEmpty nativeFuel p h rest reached core target saved
                  ((tail.1, none), head.2 ++ tail.2)
              | some recovered =>
                  let tail := foldObserved checkEmpty nativeFuel p h rest reached
                    (EnumerationExpandableIndex.frame core recovered) target saved
                  (tail.1, head.2 ++ tail.2)
          | other => (((.ok (some other), reached, saved, before.core), cache), head.2)

omit [DecidableEq Node] in
private def ValidLog (nativeFuel : Nat) (events : List (Event width)) : Prop :=
  ∀ start saved left right actual, (start, saved, left, right, actual) ∈ events →
    actual = SourceEqualityNativeDemand.execute nativeFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked

universe u v
omit [DecidableEq Node] in
private theorem prepend_exact {α : Type u} {β : Type v} {nativeFuel limit : Nat}
    {events : List (Event width)} {tail : α × List (Event width)} {original : α}
    (map : α → β) (small : events.length ≤ 1) (valid : ValidLog nativeFuel events)
    (rest : tail.1 = original ∧ tail.2.length ≤ limit ∧ ValidLog nativeFuel tail.2) :
    (map tail.1, events ++ tail.2).1 = map original ∧
    (events ++ tail.2).length ≤ limit + 1 ∧ ValidLog nativeFuel (events ++ tail.2) := by
  refine ⟨congrArg map rest.1, ?_, ?_⟩
  · rw [List.length_append]
    have laterSmall := rest.2.1
    omega
  · intro start saved left right actual member
    rcases List.mem_append.mp member with member | member
    · exact valid start saved left right actual member
    · exact rest.2.2 start saved left right actual member

private theorem cachedAdapter_exact
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) :
    let observed := cachedAdapterObserved checkEmpty nativeFuel p h caller before source target queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.cachedAdapter checkEmpty nativeFuel p h caller before source target queries ∧
    observed.2.length ≤ 1 ∧ ValidLog nativeFuel observed.2 := by
  dsimp only
  cases entry : SourcePruningEnumerationSharedDispatchQueryEvents.observe checkEmpty nativeFuel p h caller before.core source target queries with
  | mk observation events =>
      rcases observation with ⟨outcome, reached, saved⟩
      have checked := SourcePruningEnumerationSharedDispatchQueryEvents.observe_exact checkEmpty nativeFuel p h caller before.core source target queries
      simp only [entry] at checked
      rcases checked with ⟨same, small, _literal, meanings⟩
      have valid : ValidLog nativeFuel events := fun start saved left right actual member => (meanings start saved left right actual member).2.2
      cases outcome with
      | error fault =>
          simp only [cachedAdapterObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, ← same]
          exact ⟨True.intro, small, valid⟩
      | ok returned =>
          cases returned with
          | none =>
              simp only [cachedAdapterObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, ← same]
              exact ⟨True.intro, small, valid⟩
          | some action =>
              simp only [cachedAdapterObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, ← same]
              exact ⟨True.intro, small, valid⟩

private theorem rawFold_exact
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Core) (target : Nat) (queries : Queries) :
    let observed := rawFoldObserved checkEmpty nativeFuel p h sources caller before target queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty nativeFuel p h sources caller before target queries ∧
    observed.2.length ≤ sources.length ∧ ValidLog nativeFuel observed.2 := by
  dsimp only
  induction sources generalizing caller before queries with
  | nil =>
      refine ⟨rfl, Nat.le_refl 0, ?_⟩
      intro start saved left right actual member
      exact False.elim (List.not_mem_nil member)
  | cons source rest ih =>
      cases entry : SourcePruningEnumerationSharedDispatchQueryEvents.observe checkEmpty nativeFuel p h caller before source target queries with
      | mk observation events =>
          rcases observation with ⟨outcome, reached, saved⟩
          have checked := SourcePruningEnumerationSharedDispatchQueryEvents.observe_exact checkEmpty nativeFuel p h caller before source target queries
          simp only [entry] at checked
          rcases checked with ⟨same, small, _literal, meanings⟩
          have valid : ValidLog nativeFuel events := fun start saved left right actual member => (meanings start saved left right actual member).2.2
          have stopped : events.length ≤ (source :: rest).length := Nat.le_trans small (by simp)
          cases outcome with
          | error fault =>
              simp only [rawFoldObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.rawFold, ← same]
              exact ⟨True.intro, stopped, valid⟩
          | ok returned =>
              cases returned with
              | none =>
                  simp only [rawFoldObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.rawFold, ← same]
                  exact ⟨True.intro, stopped, valid⟩
              | some action =>
                  cases raw : ExceptT.run (action before) with
                  | nil =>
                      simp only [rawFoldObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.rawFold, ← same, raw]
                      exact ⟨True.intro, stopped, valid⟩
                  | cons first tail =>
                      cases first with
                      | error fault =>
                          simp only [rawFoldObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.rawFold, ← same, raw]
                          exact ⟨True.intro, stopped, valid⟩
                      | ok value =>
                          rcases value with ⟨returnedUnit, after⟩
                          cases returnedUnit
                          cases tail with
                          | nil =>
                              simp only [rawFoldObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.rawFold, ← same, raw, List.length_cons]
                              exact prepend_exact id small valid (ih reached after saved)
                          | cons second remaining =>
                              simp only [rawFoldObserved, rawHeadObserved, entry, SourcePruningEnumerationSharedCachedTerminal.rawFold, ← same, raw]
                              exact ⟨True.intro, stopped, valid⟩

/-- The complete old fold and its ordered actual query events share one execution. -/
theorem fold_observe_exact
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries) :
    let observed := foldObserved checkEmpty nativeFuel p h sources caller before target queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.fold checkEmpty nativeFuel p h sources caller before target queries ∧
    observed.2.length ≤ sources.length ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by
  dsimp only
  induction sources generalizing caller before queries with
  | nil =>
      refine ⟨rfl, Nat.le_refl 0, ?_⟩
      intro start saved left right actual member
      exact False.elim (List.not_mem_nil member)
  | cons source rest ih =>
      cases entry : cachedAdapterObserved checkEmpty nativeFuel p h caller before source target queries with
      | mk observation events =>
          rcases observation with ⟨outcome, reached, saved, cache⟩
          have checked := cachedAdapter_exact checkEmpty nativeFuel p h caller before source target queries
          simp only [entry] at checked
          rcases checked with ⟨same, small, valid⟩
          have stopped : events.length ≤ (source :: rest).length := Nat.le_trans small (by simp)
          cases outcome with
          | error fault =>
              simp only [foldObserved, entry, SourcePruningEnumerationSharedCachedTerminal.fold, ← same]
              exact ⟨True.intro, stopped, valid⟩
          | ok returned =>
              cases returned with
              | none =>
                  simp only [foldObserved, entry, SourcePruningEnumerationSharedCachedTerminal.fold, ← same]
                  exact ⟨True.intro, stopped, valid⟩
              | some raw =>
                  cases raw with
                  | nil =>
                      simp only [foldObserved, entry, SourcePruningEnumerationSharedCachedTerminal.fold, ← same]
                      exact ⟨True.intro, stopped, valid⟩
                  | cons first tail =>
                      cases first with
                      | error fault =>
                          simp only [foldObserved, entry, SourcePruningEnumerationSharedCachedTerminal.fold, ← same]
                          exact ⟨True.intro, stopped, valid⟩
                      | ok value =>
                          rcases value with ⟨returnedUnit, core⟩
                          cases returnedUnit
                          cases tail with
                          | nil =>
                              cases cache with
                              | none =>
                                  simp only [foldObserved, entry, SourcePruningEnumerationSharedCachedTerminal.fold, ← same, List.length_cons]
                                  exact prepend_exact (fun result => (result, (none : Option Cached))) small valid (rawFold_exact checkEmpty nativeFuel p h rest reached core target saved)
                              | some recovered =>
                                  simp only [foldObserved, entry, SourcePruningEnumerationSharedCachedTerminal.fold, ← same, List.length_cons]
                                  exact prepend_exact id small valid (ih reached (EnumerationExpandableIndex.frame core recovered) saved)
                          | cons second remaining =>
                              simp only [foldObserved, entry, SourcePruningEnumerationSharedCachedTerminal.fold, ← same]
                              exact ⟨True.intro, stopped, valid⟩

end MicroCFTA.SourcePruningEnumerationSharedTerminalFoldQueryEvents
