import MicroCFTA.SourcePruningEnumerationFold
import MicroCFTA.SourcePruningEnumerationDispatchUnique

/-!
# Exact successful fold observations

Different successful bounds retain every returned field.
Each singleton action continues from the same core and caller.
Every other raw shape stops with the same observation.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

private theorem ok_tuple_unique
    {E : Type _} {A : Type _} {B : Type _} {C : Type _} {D : Type _}
    {observation : Except E A × B × C × D}
    {first second : A} {after later : B} {saved current : C} {core nextCore : D}
    (one : observation = (.ok first, after, saved, core))
    (two : observation = (.ok second, later, current, nextCore)) :
    first = second ∧ after = later ∧ saved = current ∧ core = nextCore := by
  simpa only [Prod.mk.injEq, Except.ok.injEq] using one.symm.trans two

/-- Successful bounds identify the full result, caller, query memo and outer core. -/
theorem ok_unique
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (flag : Bool) {n p h N P H : Nat} {sources : List Nat}
    {beforeCaller : Caller width} {before : EnumerationState.State Symbol EnumGuard}
    {target : Nat} {queries : Queries}
    {result other : Option (List (Except EnumerationState.Error
      (Unit × EnumerationState.State Symbol EnumGuard)))}
    {afterCaller later : Caller width} {saved current : Queries}
    {after laterCore : EnumerationState.State Symbol EnumGuard}
    (one : run flag n p h sources beforeCaller before target queries =
      (.ok result, afterCaller, saved, after))
    (two : run flag N P H sources beforeCaller before target queries =
      (.ok other, later, current, laterCore)) :
    result = other ∧ afterCaller = later ∧ saved = current ∧ after = laterCore := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run] at one two
      exact ok_tuple_unique one two
  | cons source rest ih =>
      rcases firstDispatch : SourcePruningEnumerationDispatch.dispatch flag n p h
          beforeCaller before source target queries with ⟨firstOutcome, headCaller, headQueries⟩
      cases firstOutcome with
      | error fault =>
          simp only [run, firstDispatch] at one
          cases one
      | ok selected =>
          rcases secondDispatch : SourcePruningEnumerationDispatch.dispatch flag N P H
              beforeCaller before source target queries with ⟨secondOutcome, otherCaller, otherQueries⟩
          cases secondOutcome with
          | error fault =>
              simp only [run, secondDispatch] at two
              cases two
          | ok otherSelected =>
              obtain ⟨sameSelected, sameCaller, sameQueries⟩ :=
                SourcePruningEnumerationDispatch.ok_unique flag firstDispatch secondDispatch
              subst otherSelected
              subst otherCaller
              subst otherQueries
              cases selected with
              | none =>
                  simp only [run, firstDispatch] at one
                  simp only [run, secondDispatch] at two
                  exact ok_tuple_unique one two
              | some action =>
                  cases raw : ExceptT.run (action before) with
                  | nil =>
                      simp only [run, firstDispatch, raw] at one
                      simp only [run, secondDispatch, raw] at two
                      exact ok_tuple_unique one two
                  | cons first tail =>
                      cases first with
                      | error fault =>
                          simp only [run, firstDispatch, raw] at one
                          simp only [run, secondDispatch, raw] at two
                          exact ok_tuple_unique one two
                      | ok pair =>
                          rcases pair with ⟨token, middle⟩
                          cases token
                          cases tail with
                          | nil =>
                              simp only [run, firstDispatch, raw] at one
                              simp only [run, secondDispatch, raw] at two
                              exact ih (beforeCaller := headCaller) (before := middle)
                                (queries := headQueries) one two
                          | cons second remaining =>
                              simp only [run, firstDispatch, raw] at one
                              simp only [run, secondDispatch, raw] at two
                              exact ok_tuple_unique one two

end MicroCFTA.SourcePruningEnumerationFold
