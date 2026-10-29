import MicroCFTA.SourcePruningEnumerationAncestryExtension
import MicroCFTA.SourcePruningEnumerationDispatchShape
import MicroCFTA.SourcePruningEnumerationCachedAdapter

/-!
# All-slot ancestry through actual dispatch and cache adaptation

The actual singleton dispatch keeps each old per-slot recursion key.
Cache adaptation returns the original core or that actual singleton core.
Both cases retain the exact expansion history.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationAncestryExtension
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- The actual raw singleton extends every slot and retains expansion ancestry. -/
theorem dispatch_ancestry_extension
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (selected : dispatch checkEmpty nativeFuel p h beforeCaller before source target queries =
      (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    Extends before after ∧ after.expansionAncestry = before.expansionAncestry := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨_different, _sourceNode, _targetNode, merged, sourceScs, targetScs,
      _sourceStored, _targetStored, rfl⟩
  · exact ⟨Extends.refl _, rfl⟩
  · exact ⟨Extends.assimilated before target source
      (.unenumerated merged (sourceScs ++ targetScs)), rfl⟩

end MicroCFTA.SourcePruningEnumerationDispatch

namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos

private theorem recovered_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {returned : Core}
    (fields : Extends before.core returned ∧
      returned.expansionAncestry = before.core.expansionAncestry)
    (recovered : (returned.values[target]?).bind (fun value =>
      (SourcePruningEnumerationNativeIndex.candidate heap value).map (fun flag =>
        (⟨returned, (fun slot => if slot = source then false else
          if slot = target then flag else before.expandable slot), before.waiting⟩ : Cached))) = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  obtain ⟨value, _stored, classified⟩ := Option.bind_eq_some_iff.mp recovered
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp classified
  subst after
  exact fields

private theorem adapt_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {raw : Raw}
    (rows : ∀ returned, raw = [.ok ((), returned)] → Extends before.core returned ∧
      returned.expansionAncestry = before.core.expansionAncestry)
    (adapted : adapt heap before source target raw = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  cases raw with
  | nil =>
      simp only [adapt, Option.some.injEq] at adapted
      subst after
      exact ⟨Extends.refl _, rfl⟩
  | cons row rest =>
      cases row with
      | error fault => simp only [adapt] at adapted; cases adapted
      | ok payload =>
          rcases payload with ⟨ignored, returned⟩
          cases ignored
          cases rest with
          | cons next later => simp only [adapt] at adapted; cases adapted
          | nil =>
              have returnedFields := rows returned rfl
              by_cases same : source = target
              · simp only [adapt, same, ↓reduceIte, Option.some.injEq] at adapted
                subst after
                exact ⟨Extends.refl _, rfl⟩
              · cases stored : before.core.values[source]? with
                | none =>
                    simp only [adapt, same, ↓reduceIte, stored] at adapted
                    exact recovered_ancestry_extension returnedFields adapted
                | some value =>
                    cases value with
                    | eliminated =>
                        simp only [adapt, same, ↓reduceIte, stored, Option.some.injEq] at adapted
                        subst after
                        exact ⟨Extends.refl _, rfl⟩
                    | enumerated fragment =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_ancestry_extension returnedFields adapted
                    | unenumerated node scs =>
                        simp only [adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_ancestry_extension returnedFields adapted

variable {width : Nat}

/-- Actual dispatch rows and attached caches retain all old keys and expansion ancestry. -/
theorem run_ancestry_extension
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) :
    (∀ returned, (run checkEmpty nativeFuel p h caller before source target queries).1 =
      .ok (some [.ok ((), returned)]) → Extends before.core returned ∧
      returned.expansionAncestry = before.core.expansionAncestry) ∧
    (∀ after, (run checkEmpty nativeFuel p h caller before source target queries).2.2.2 = some after →
      Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry) := by
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
              Extends before.core returned ∧
              returned.expansionAncestry = before.core.expansionAncestry := by
            intro returned completed
            exact SourcePruningEnumerationDispatch.dispatch_ancestry_extension checkEmpty nativeFuel p h
              caller before.core source target queries action reachedCaller saved returned dispatched completed
          constructor
          · intro returned same
            exact rows returned (Option.some.inj (Except.ok.inj same))
          · intro after adapted
            exact adapt_ancestry_extension rows adapted

end MicroCFTA.SourcePruningEnumerationCachedAdapter
