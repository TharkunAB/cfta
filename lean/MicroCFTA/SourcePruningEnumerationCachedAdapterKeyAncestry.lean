import MicroCFTA.SourcePruningEnumerationDispatchKeyAncestry
import MicroCFTA.SourcePruningEnumerationCachedAdapter

/-!
# Historical key shapes through actual dispatch cache adaptation

The dispatcher derives each successful row from the original carrier.
The private adapter proof identifies the same returned core.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
open EnumerationState SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {carrier : List (List (List (List Nat)))}

private theorem recovered_key_ancestry
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {returned : Core} (valid : KeyAncestry carrier returned)
    (recovered : (returned.values[target]?).bind (fun value =>
      (SourcePruningEnumerationNativeIndex.candidate heap value).map (fun flag =>
        (⟨returned, (fun slot => if slot = source then false else
          if slot = target then flag else before.expandable slot), before.waiting⟩ : Cached))) = some after) :
    KeyAncestry carrier after.core := by
  obtain ⟨value, _stored, classified⟩ := Option.bind_eq_some_iff.mp recovered
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp classified
  subst after
  exact valid

/-- An actual adapter keeps the old carrier or the derived singleton carrier. -/
private theorem adapt_key_ancestry
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {raw : Raw} (valid : KeyAncestry carrier before.core)
    (rows : ∀ returned, raw = [.ok ((), returned)] → KeyAncestry carrier returned)
    (adapted : adapt heap before source target raw = some after) : KeyAncestry carrier after.core := by
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
                    exact recovered_key_ancestry returnedValid adapted
                | some value =>
                    cases value with
                    | eliminated =>
                        simp only [adapt, same, ↓reduceIte, stored, Option.some.injEq] at adapted
                        subst after
                        exact valid
                    | enumerated fragment =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_key_ancestry returnedValid adapted
                    | unenumerated node scs =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_key_ancestry returnedValid adapted

variable {width : Nat}

/-- Actual dispatcher execution retains the carrier at singleton rows and attached caches. -/
theorem run_key_ancestry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) (valid : KeyAncestry carrier before.core) :
    (∀ returned, (run checkEmpty nativeFuel p h caller before source target queries).1 =
      .ok (some [.ok ((), returned)]) → KeyAncestry carrier returned) ∧
    (∀ after, (run checkEmpty nativeFuel p h caller before source target queries).2.2.2 = some after →
      KeyAncestry carrier after.core) := by
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
              KeyAncestry carrier returned := by
            intro returned completed
            exact SourcePruningEnumerationDispatch.dispatch_key_ancestry checkEmpty nativeFuel p h
              caller before.core source target queries action reachedCaller saved returned
              valid dispatched completed
          constructor
          · intro returned same
            exact rows returned (Option.some.inj (Except.ok.inj same))
          · intro after adapted
            exact adapt_key_ancestry valid rows adapted

end MicroCFTA.SourcePruningEnumerationCachedAdapter
