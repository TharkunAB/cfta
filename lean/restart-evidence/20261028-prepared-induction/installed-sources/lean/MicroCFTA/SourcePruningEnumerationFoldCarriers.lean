import MicroCFTA.SourcePruningEnumerationAssimilationCarriers
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Carriers at every actual native fold endpoint

The terminal prefix supplies the recorded source classes.
Successful singleton actions retain that forest and transfer each carrier.
Every other action outcome retains the reached enumeration prefix.
Attached caches retain either that prefix or the same singleton core.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness EnumerationCarriers EnumerationGraphReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- All actual outer fold outcomes retain carriers and reference provenance. -/
theorem run_carriers
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (total : UnionFind.Total before.representatives)
    (related : ∀ source ∈ sources, UnionFind.SameClass before.representatives target source)
    (references : ReferencesCarry before)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨total, .refl before, references⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨total, .refl before, references⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨total, .refl before, references⟩
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨total, .refl before, references⟩
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact ⟨total, .refl before, references⟩
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          obtain ⟨forest, middleTotal, middleCarriers, middleReferences⟩ :=
                            SourcePruningEnumerationDispatch.dispatch_carriers checkEmpty nativeFuel p h
                              beforeCaller before source target queries action reachedCaller saved middle
                              total (related source (by simp)) references dispatchObserved rawObserved
                          have tailRelated : ∀ other ∈ rest,
                              UnionFind.SameClass middle.representatives target other := by
                            intro other member
                            rw [forest]
                            exact related other (List.mem_cons_of_mem source member)
                          simp only [run, dispatchObserved, rawObserved] at observed
                          obtain ⟨afterTotal, tailCarriers, afterReferences⟩ :=
                            ih reachedCaller middle saved middleTotal tailRelated middleReferences observed
                          exact ⟨afterTotal, middleCarriers.trans tailCarriers, afterReferences⟩
                      | cons second remaining =>
                          simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact ⟨total, .refl before, references⟩

end MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
open EnumerationState EnumerationCorrectness EnumerationCarriers EnumerationGraphReferences InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos

private theorem recovered_carriers
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {returned : Core}
    (valid : returned.representatives = before.core.representatives ∧
      UnionFind.Total returned.representatives ∧ PreservesCarriers before.core returned ∧ ReferencesCarry returned)
    (recovered : (returned.values[target]?).bind (fun value =>
      (SourcePruningEnumerationNativeIndex.candidate heap value).map (fun flag =>
        (⟨returned, (fun slot => if slot = source then false else
          if slot = target then flag else before.expandable slot), before.waiting⟩ : Cached))) = some after) :
    after.core.representatives = before.core.representatives ∧
      UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  obtain ⟨value, _stored, classified⟩ := Option.bind_eq_some_iff.mp recovered
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp classified
  subst after
  exact valid

/-- The actual adapter retains the old carrier state or its actual singleton state. -/
theorem adapt_carriers
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {raw : Raw} (total : UnionFind.Total before.core.representatives)
    (references : ReferencesCarry before.core)
    (rows : ∀ returned, raw = [.ok ((), returned)] →
      returned.representatives = before.core.representatives ∧
        UnionFind.Total returned.representatives ∧ PreservesCarriers before.core returned ∧ ReferencesCarry returned)
    (adapted : adapt heap before source target raw = some after) :
    after.core.representatives = before.core.representatives ∧
      UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  cases raw with
  | nil =>
      simp only [adapt, Option.some.injEq] at adapted
      subst after
      exact ⟨rfl, total, .refl before.core, references⟩
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
                exact ⟨rfl, total, .refl before.core, references⟩
              · cases stored : before.core.values[source]? with
                | none =>
                    simp only [adapt, same, ↓reduceIte, stored] at adapted
                    exact recovered_carriers returnedValid adapted
                | some value =>
                    cases value with
                    | eliminated =>
                        simp only [adapt, same, ↓reduceIte, stored, Option.some.injEq] at adapted
                        subst after
                        exact ⟨rfl, total, .refl before.core, references⟩
                    | enumerated fragment =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_carriers returnedValid adapted
                    | unenumerated node scs =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_carriers returnedValid adapted

variable {width : Nat}

/-- Actual singleton rows and all attached adapter caches retain their original carriers. -/
theorem run_carriers
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) (total : UnionFind.Total before.core.representatives)
    (related : UnionFind.SameClass before.core.representatives target source)
    (references : ReferencesCarry before.core) :
    (∀ returned, (run checkEmpty nativeFuel p h caller before source target queries).1 =
      .ok (some [.ok ((), returned)]) →
      returned.representatives = before.core.representatives ∧
        UnionFind.Total returned.representatives ∧ PreservesCarriers before.core returned ∧ ReferencesCarry returned) ∧
    (∀ after, (run checkEmpty nativeFuel p h caller before source target queries).2.2.2 = some after →
      after.core.representatives = before.core.representatives ∧
        UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
        ReferencesCarry after.core) := by
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
              returned.representatives = before.core.representatives ∧
                UnionFind.Total returned.representatives ∧ PreservesCarriers before.core returned ∧ ReferencesCarry returned := by
            intro returned completed
            exact SourcePruningEnumerationDispatch.dispatch_carriers checkEmpty nativeFuel p h
              caller before.core source target queries action reachedCaller saved returned
              total related references dispatched completed
          constructor
          · intro returned same
            exact rows returned (Option.some.inj (Except.ok.inj same))
          · intro after adapted
            exact adapt_carriers total references rows adapted

end MicroCFTA.SourcePruningEnumerationCachedAdapter

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState EnumerationCarriers EnumerationGraphReferences InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Exact cache erasure retains carriers at every actual cached-fold outer core. -/
theorem carriers
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (total : UnionFind.Total before.core.representatives)
    (related : ∀ source ∈ sources, UnionFind.SameClass before.core.representatives target source)
    (references : ReferencesCarry before.core) :
    UnionFind.Total (run checkEmpty nativeFuel p h sources caller before target queries).1.2.2.2.representatives ∧
      PreservesCarriers before.core (run checkEmpty nativeFuel p h sources caller before target queries).1.2.2.2 ∧
      ReferencesCarry (run checkEmpty nativeFuel p h sources caller before target queries).1.2.2.2 := by
  exact SourcePruningEnumerationFold.run_carriers checkEmpty nativeFuel p h sources
    caller before.core target queries
    (run checkEmpty nativeFuel p h sources caller before target queries).1.1
    (run checkEmpty nativeFuel p h sources caller before target queries).1.2.1
    (run checkEmpty nativeFuel p h sources caller before target queries).1.2.2.1
    (run checkEmpty nativeFuel p h sources caller before target queries).1.2.2.2
    total related references (erase checkEmpty nativeFuel p h sources caller before target queries).symm

/-- Every actual attached fold cache retains carriers, including a rejected prefix. -/
theorem candidate_carriers
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (total : UnionFind.Total before.core.representatives)
    (related : ∀ source ∈ sources, UnionFind.SameClass before.core.representatives target source)
    (references : ReferencesCarry before.core) (after : Cached)
    (candidate : (run checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [run, Option.some.injEq] at candidate
      subst after
      exact ⟨total, .refl before.core, references⟩
  | cons source rest ih =>
      have headCarriers := SourcePruningEnumerationCachedAdapter.run_carriers
        checkEmpty nativeFuel p h caller before source target queries total
          (related source (by simp)) references
      rcases headObserved : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headCarriers
      dsimp only at headCarriers
      cases outcome with
      | error fault => simp only [run, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [run, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [run, headObserved] at candidate
                  exact (headCarriers.2 after candidate).2
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [run, headObserved] at candidate
                      exact (headCarriers.2 after candidate).2
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [run, headObserved] at candidate
                          exact (headCarriers.2 after candidate).2
                      | nil =>
                          have coreCarriers := headCarriers.1 core rfl
                          have tailRelated : ∀ other ∈ rest,
                              UnionFind.SameClass core.representatives target other := by
                            intro other member
                            rw [coreCarriers.1]
                            exact related other (List.mem_cons_of_mem source member)
                          cases headCache with
                          | none => simp only [run, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [run, headObserved] at candidate
                              obtain ⟨afterTotal, tailCarriers, afterReferences⟩ :=
                                ih reachedCaller (EnumerationExpandableIndex.frame core recovered) saved
                                  coreCarriers.2.1 tailRelated coreCarriers.2.2.2 candidate
                              exact ⟨afterTotal, coreCarriers.2.2.1.trans tailCarriers, afterReferences⟩

end MicroCFTA.SourcePruningEnumerationCachedFold
