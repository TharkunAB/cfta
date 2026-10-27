import MicroCFTA.SourcePruningEnumerationDispatchCanonical
import MicroCFTA.SourcePruningEnumerationCachedAdapter

namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
open EnumerationState EnumerationValidity InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos

private theorem recovered_canonical
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {returned : Core} (valid : Canonical returned)
    (recovered : (returned.values[target]?).bind (fun value =>
      (SourcePruningEnumerationNativeIndex.candidate heap value).map (fun flag =>
        (⟨returned, (fun slot => if slot = source then false else
          if slot = target then flag else before.expandable slot), before.waiting⟩ : Cached))) = some after) :
    Canonical after.core := by
  obtain ⟨value, _stored, classified⟩ := Option.bind_eq_some_iff.mp recovered
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp classified
  subst after
  exact valid

/-- The actual adapter retains a canonical old cache or a canonical singleton core. -/
theorem adapt_canonical
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {raw : Raw} (valid : Canonical before.core)
    (rows : ∀ returned, raw = [.ok ((), returned)] → Canonical returned)
    (adapted : adapt heap before source target raw = some after) : Canonical after.core := by
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
                    exact recovered_canonical returnedValid adapted
                | some value =>
                    cases value with
                    | eliminated =>
                        simp only [adapt, same, ↓reduceIte, stored, Option.some.injEq] at adapted
                        subst after
                        exact valid
                    | enumerated fragment =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_canonical returnedValid adapted
                    | unenumerated node scs =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_canonical returnedValid adapted

variable {width : Nat}

/-- Every actual singleton core and every attached cache retain canonical suspended tries. -/
theorem run_canonical
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) (valid : Canonical before.core) :
    (∀ returned, (run checkEmpty nativeFuel p h caller before source target queries).1 =
      .ok (some [.ok ((), returned)]) → Canonical returned) ∧
    (∀ after, (run checkEmpty nativeFuel p h caller before source target queries).2.2.2 = some after →
      Canonical after.core) := by
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
              Canonical returned := by
            intro returned completed
            exact SourcePruningEnumerationDispatch.dispatch_canonical checkEmpty nativeFuel p h
              caller before.core source target queries action reachedCaller saved returned
              valid dispatched completed
          constructor
          · intro returned same
            exact rows returned (Option.some.inj (Except.ok.inj same))
          · intro after adapted
            exact adapt_canonical valid rows adapted

end MicroCFTA.SourcePruningEnumerationCachedAdapter
