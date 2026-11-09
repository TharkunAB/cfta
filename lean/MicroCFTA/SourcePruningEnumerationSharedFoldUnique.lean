import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
import MicroCFTA.SourcePruningEnumerationSharedDispatchUnique

/-!
# Exact successful shared fold observations

Different successful bounds retain every returned field.
Each singleton action continues from the same core and caller.
Every other raw shape stops with the same observation.
Cache erasure identifies only the primary raw observation. It does not
identify private cache candidates across different bounds.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

private theorem ok_tuple_unique
    {E : Type _} {A : Type _} {B : Type _} {C : Type _} {D : Type _}
    {observation : Except E A × B × C × D}
    {first second : A} {after later : B} {saved current : C} {core nextCore : D}
    (one : observation = (.ok first, after, saved, core))
    (two : observation = (.ok second, later, current, nextCore)) :
    first = second ∧ after = later ∧ saved = current ∧ core = nextCore := by
  simpa only [Prod.mk.injEq, Except.ok.injEq] using one.symm.trans two

/-- Successful bounds identify the full result, caller, query memo and outer core. -/
theorem rawFold_ok_unique
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (flag : Bool) {n p h N P H : Nat} {sources : List Nat}
    {beforeCaller : Caller width} {before : EnumerationState.State Symbol Constraint}
    {target : Nat} {queries : Queries}
    {result other : Option (List (Except EnumerationState.Error
      (Unit × EnumerationState.State Symbol Constraint)))}
    {afterCaller later : Caller width} {saved current : Queries}
    {after laterCore : EnumerationState.State Symbol Constraint}
    (one : rawFold flag n p h sources beforeCaller before target queries =
      (.ok result, afterCaller, saved, after))
    (two : rawFold flag N P H sources beforeCaller before target queries =
      (.ok other, later, current, laterCore)) :
    result = other ∧ afterCaller = later ∧ saved = current ∧ after = laterCore := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [rawFold] at one two
      exact ok_tuple_unique one two
  | cons source rest ih =>
      rcases firstDispatch : SourcePruningEnumerationSharedDispatch.dispatch flag n p h
          beforeCaller before source target queries with ⟨firstOutcome, headCaller, headQueries⟩
      cases firstOutcome with
      | error fault =>
          simp only [rawFold, firstDispatch] at one
          cases one
      | ok selected =>
          rcases secondDispatch : SourcePruningEnumerationSharedDispatch.dispatch flag N P H
              beforeCaller before source target queries with ⟨secondOutcome, otherCaller, otherQueries⟩
          cases secondOutcome with
          | error fault =>
              simp only [rawFold, secondDispatch] at two
              cases two
          | ok otherSelected =>
              obtain ⟨sameSelected, sameCaller, sameQueries⟩ :=
                SourcePruningEnumerationSharedDispatch.ok_unique flag firstDispatch secondDispatch
              subst otherSelected
              subst otherCaller
              subst otherQueries
              cases selected with
              | none =>
                  simp only [rawFold, firstDispatch] at one
                  simp only [rawFold, secondDispatch] at two
                  exact ok_tuple_unique one two
              | some action =>
                  cases raw : ExceptT.run (action before) with
                  | nil =>
                      simp only [rawFold, firstDispatch, raw] at one
                      simp only [rawFold, secondDispatch, raw] at two
                      exact ok_tuple_unique one two
                  | cons first tail =>
                      cases first with
                      | error fault =>
                          simp only [rawFold, firstDispatch, raw] at one
                          simp only [rawFold, secondDispatch, raw] at two
                          exact ok_tuple_unique one two
                      | ok pair =>
                          rcases pair with ⟨token, middle⟩
                          cases token
                          cases tail with
                          | nil =>
                              simp only [rawFold, firstDispatch, raw] at one
                              simp only [rawFold, secondDispatch, raw] at two
                              exact ih (beforeCaller := headCaller) (before := middle)
                                (queries := headQueries) one two
                          | cons second remaining =>
                              simp only [rawFold, firstDispatch, raw] at one
                              simp only [rawFold, secondDispatch, raw] at two
                              exact ok_tuple_unique one two

/-- Successful cache-fold observations identify every field of the actual raw return. -/
theorem fold_ok_unique
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (flag : Bool) {n p h N P H : Nat} {sources : List Nat}
    {beforeCaller : Caller width} {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    {target : Nat} {queries : Queries}
    {result other : Option (List (Except EnumerationState.Error
      (Unit × EnumerationState.State Symbol Constraint)))}
    {afterCaller later : Caller width} {saved current : Queries}
    {after laterCore : EnumerationState.State Symbol Constraint}
    (one : (fold flag n p h sources beforeCaller before target queries).1 =
      (.ok result, afterCaller, saved, after))
    (two : (fold flag N P H sources beforeCaller before target queries).1 =
      (.ok other, later, current, laterCore)) :
    result = other ∧ afterCaller = later ∧ saved = current ∧ after = laterCore := by
  rw [fold_erase] at one two
  exact rawFold_ok_unique flag one two

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
