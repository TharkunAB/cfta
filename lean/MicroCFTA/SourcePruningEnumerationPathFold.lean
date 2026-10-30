import MicroCFTA.SourcePruningEnumerationPathAssimilation
import MicroCFTA.SourcePruningEnumerationPathStorage
import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.SourcePruningEnumerationCachedAdapter
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Model-free paths through the actual cached adapter and child fold

Each successful singleton action preserves the stored path predicate.
Every other fold outcome retains the current prefix core.
The attached-cache result also covers rejected prefixes.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
open EnumerationState SourcePruningEnumerationPathTransport InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {P : EqualityTrie.Path → Prop}

private theorem recovered_paths
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {returned : Core} (valid : StatePaths P returned)
    (recovered : (returned.values[target]?).bind (fun value =>
      (SourcePruningEnumerationNativeIndex.candidate heap value).map (fun flag =>
        (⟨returned, (fun slot => if slot = source then false else
          if slot = target then flag else before.expandable slot), before.waiting⟩ : Cached))) = some after) :
    StatePaths P after.core := by
  obtain ⟨value, _stored, classified⟩ := Option.bind_eq_some_iff.mp recovered
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp classified
  subst after
  exact valid

/-- The actual adapter retains paths from the old cache or its singleton core. -/
theorem adapt_paths
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {raw : Raw} (valid : StatePaths P before.core)
    (rows : ∀ returned, raw = [.ok ((), returned)] → StatePaths P returned)
    (adapted : adapt heap before source target raw = some after) : StatePaths P after.core := by
  cases raw with
  | nil =>
      simp only [adapt, Option.some.injEq] at adapted
      subst after
      exact valid
  | cons row rest =>
      cases row with
      | error fault => simp only [adapt] at adapted; cases adapted
      | ok payload =>
          rcases payload with ⟨ignored, returned⟩
          cases ignored
          cases rest with
          | cons next later => simp only [adapt] at adapted; cases adapted
          | nil =>
              have returnedValid := rows returned rfl
              by_cases same : source = target
              · simp only [adapt, same, ↓reduceIte, Option.some.injEq] at adapted
                subst after
                exact valid
              · cases stored : before.core.values[source]? with
                | none =>
                    simp only [adapt, same, ↓reduceIte, stored] at adapted
                    exact recovered_paths returnedValid adapted
                | some value =>
                    cases value with
                    | eliminated =>
                        simp only [adapt, same, ↓reduceIte, stored, Option.some.injEq] at adapted
                        subst after
                        exact valid
                    | enumerated fragment =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_paths returnedValid adapted
                    | unenumerated node scs =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_paths returnedValid adapted

variable {width : Nat}

/-- Every actual singleton core and attached cache retains the path predicate. -/
theorem run_paths
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) (valid : StatePaths P before.core) :
    (∀ returned, (run checkEmpty nativeFuel p h caller before source target queries).1 =
      .ok (some [.ok ((), returned)]) → StatePaths P returned) ∧
    (∀ after, (run checkEmpty nativeFuel p h caller before source target queries).2.2.2 = some after →
      StatePaths P after.core) := by
  rcases dispatched : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
    caller before.core source target queries with ⟨outcome, reachedCaller, saved⟩
  cases outcome with
  | error fault =>
      simp only [run, dispatched]
      constructor <;> intro after impossible <;> cases impossible
  | ok possible =>
      cases possible with
      | none =>
          simp only [run, dispatched]
          constructor <;> intro after impossible <;> cases impossible
      | some action =>
          simp only [run, dispatched]
          have rows : ∀ returned, ExceptT.run (action before.core) = [.ok ((), returned)] →
              StatePaths P returned := by
            intro returned completed
            exact SourcePruningEnumerationDispatch.dispatch_paths checkEmpty nativeFuel p h
              caller before.core source target queries action reachedCaller saved returned
              valid dispatched completed
          constructor
          · intro returned same
            exact rows returned (Option.some.inj (Except.ok.inj same))
          · intro after adapted
            exact adapt_paths valid rows adapted

end MicroCFTA.SourcePruningEnumerationCachedAdapter

namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness SourcePruningEnumerationPathTransport
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat} {P : EqualityTrie.Path → Prop}

/-- Every fixed-bound fold outcome retains the path predicate at its outer core. -/
theorem run_paths
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (proper : StatePaths P before)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) : StatePaths P after := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact proper
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact proper
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact proper
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact proper
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact proper
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          have middleProper := SourcePruningEnumerationDispatch.dispatch_paths
                            checkEmpty nativeFuel p h beforeCaller before source target queries action
                            reachedCaller saved middle proper dispatchObserved rawObserved
                          simp only [run, dispatchObserved, rawObserved] at observed
                          exact ih reachedCaller middle saved middleProper observed
                      | cons second remaining =>
                          simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact proper

end MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat} {P : EqualityTrie.Path → Prop}

/-- Cache erasure retains the path predicate at the cached-fold outer core. -/
theorem paths
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) (valid : StatePaths P before.core) :
    StatePaths P (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2 := by
  exact SourcePruningEnumerationFold.run_paths checkEmpty nativeFuel p h sources
    beforeCaller before.core target queries
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2
    valid (erase checkEmpty nativeFuel p h sources beforeCaller before target queries).symm

end MicroCFTA.SourcePruningEnumerationCachedFold

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState SourcePruningEnumerationPathTransport InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat} {P : EqualityTrie.Path → Prop}

/-- Every attached fold cache retains paths, including a rejected prefix cache. -/
theorem candidate_paths
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (valid : StatePaths P before.core) (after : Cached)
    (candidate : (run checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    StatePaths P after.core := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [run, Option.some.injEq] at candidate
      subst after
      exact valid
  | cons source rest ih =>
      have headProper := SourcePruningEnumerationCachedAdapter.run_paths
        checkEmpty nativeFuel p h caller before source target queries valid
      rcases headObserved : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headProper
      dsimp only at headProper
      cases outcome with
      | error fault => simp only [run, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [run, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [run, headObserved] at candidate
                  exact headProper.2 after candidate
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [run, headObserved] at candidate
                      exact headProper.2 after candidate
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [run, headObserved] at candidate
                          exact headProper.2 after candidate
                      | nil =>
                          have coreProper := headProper.1 core rfl
                          cases headCache with
                          | none => simp only [run, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [run, headObserved] at candidate
                              exact ih reachedCaller (EnumerationExpandableIndex.frame core recovered)
                                saved coreProper candidate

end MicroCFTA.SourcePruningEnumerationCachedFold

namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness SourcePruningEnumerationPathTransport EnumerationSchedule
open SourcePruningEnumerationPathStorage
variable {P : EqualityTrie.Path → Prop}

attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- Every actual successful terminal prefix retains the stored path predicate. -/
theorem run_paths
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State SourcePruningTemplates.Symbol EnumGuard)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (proper : (StatePaths P) before)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    (StatePaths P) after := by
  unfold run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedProper := mapM_invariant (fun sc => representative fuel sc.var) (StatePaths P) (first :: rest)
    (fun sc _ previous result next valid step => representative_paths fuel sc.var result previous next valid step)
    before scanned actualRecorded proper scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedProper := forM_invariant (fun sc => unionVariables fuel first.var sc.var) (StatePaths P) rest
    (fun sc _ previous next valid step => unionVariables_paths fuel first.var sc.var previous next valid step)
    scanned united scannedProper unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedProper := representative_paths fuel first.var actualWinner united resolved
    unitedProper resolution
  obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
  exact resolvedProper

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
