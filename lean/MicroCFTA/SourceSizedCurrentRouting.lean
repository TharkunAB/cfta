import MicroCFTA.SourceSizedBoundedApiLaws

/-!
# Current Sized route control

`Data/CFTA/Sized.hs:149-175` maps routing over `referenceStates`.
A missing map key selects empty classes. A failed table helper selects
the reference API. A returned helper selects its own API. A residual
reference error prevents every route, including a missing map key.

This file proves control and value laws only. Actual `tableClasses`
computation, count and intersection tables, ambiguity checks, and native
map storage remain separate. Missing keys are not claimed to have an
empty language in the unrestricted original automaton.
-/
namespace MicroCFTA.SourceSizedCurrentRouting
open Language SourceSizedDispatcher

variable {State Symbol Error : Type}

/-- The missing-state route uses the actual constant empty class callback. -/
def emptyApi [DecidableEq Symbol] : Api Symbol :=
  SourceSizedBoundedApiLaws.fromClasses (fun _ => [])

private theorem empty_reference [DecidableEq Symbol] :
    emptyApi (Symbol := Symbol) = referenceApi (fun _ : Unit => []) () := by
  have classes_nil (size : Nat) :
      SourceSizedReference.classes (fun _ : Unit => []) size () = ([] : List (Term Symbol)) := by
    cases size with
    | zero => exact SourceSizedReference.classes_zero _ _
    | succ remaining =>
      rw [SourceSizedReference.classes_succ]
      rfl
  have same :
      (fun size => SourceSizedReference.classes (fun _ : Unit => []) size ()) =
        (fun _ : Nat => ([] : List (Term Symbol))) := funext classes_nil
  change SourceSizedBoundedApiLaws.fromClasses (fun _ => []) =
    SourceSizedBoundedApiLaws.fromClasses
      (fun size => SourceSizedReference.classes (fun _ : Unit => []) size ())
  rw [same]

/-- The empty route satisfies every exact API law for the empty language. -/
theorem empty_exact [DecidableEq Symbol] :
    SourceSizedApiLaws.Exact (emptyApi (Symbol := Symbol)) (fun _ => False) := by
  rw [empty_reference]
  apply SourceSizedApiLaws.reference
  intro term
  constructor
  · intro accepted
    cases accepted with
    | node edge arguments member _ _ => cases member
  · intro impossible
    exact False.elim impossible

/-- All signed size and rank queries of the empty callback are empty. -/
theorem empty_observables [DecidableEq Symbol] (size index : Int) (term : Term Symbol) :
    (emptyApi (Symbol := Symbol)).terms size = [] ∧
      (emptyApi (Symbol := Symbol)).count size = 0 ∧
      (emptyApi (Symbol := Symbol)).unrank size index = none ∧
      (emptyApi (Symbol := Symbol)).rank term = none := by
  simp [emptyApi, SourceSizedBoundedApiLaws.fromClasses,
    SourceSizedQueries.termsSigned, SourceSizedQueries.countSigned,
    SourceSizedQueries.unrankSigned, SourceSizedQueries.rank, SizedRank.rankOf]

/-- Preserve both map absence and helper failure as distinct source cases. -/
def route [DecidableEq Symbol] (lookup : State → Option (Option (Api Symbol)))
    (reference : State → Api Symbol) (state : State) : Api Symbol :=
  match lookup state with
  | none => emptyApi
  | some none => reference state
  | some (some api) => api

/-- A missing map key uses empty classes. -/
theorem route_missing [DecidableEq Symbol] (lookup : State → Option (Option (Api Symbol)))
    (reference : State → Api Symbol) (state : State) (missing : lookup state = none) :
    route lookup reference state = emptyApi := by
  simp only [route, missing]

/-- A present key whose table helper failed uses the reference API. -/
theorem route_reference [DecidableEq Symbol] (lookup : State → Option (Option (Api Symbol)))
    (reference : State → Api Symbol) (state : State) (failed : lookup state = some none) :
    route lookup reference state = reference state := by
  simp only [route, failed]

/-- A present successful helper supplies the selected API unchanged. -/
theorem route_prepared [DecidableEq Symbol] (lookup : State → Option (Option (Api Symbol)))
    (reference : State → Api Symbol) (state : State) (api : Api Symbol)
    (prepared : lookup state = some (some api)) :
    route lookup reference state = api := by
  simp only [route, prepared]

/-- Map routes over the global reference result, as the source does. -/
def dispatch [DecidableEq Symbol] (lookup : State → Option (Option (Api Symbol)))
    (reference : Except Error (State → Api Symbol)) : Except Error (State → Api Symbol) :=
  reference.map (fun api => route lookup api)

/-- A global reference error precedes every state lookup. -/
theorem dispatch_error [DecidableEq Symbol] (lookup : State → Option (Option (Api Symbol)))
    (failure : Error) : dispatch lookup (.error failure) = .error failure := rfl

/-- Only a successful reference result produces the per-state routing function. -/
theorem dispatch_ok [DecidableEq Symbol] (lookup : State → Option (Option (Api Symbol)))
    (reference : State → Api Symbol) :
    dispatch (Error := Error) lookup (.ok reference) = .ok (route lookup reference) := rfl

end MicroCFTA.SourceSizedCurrentRouting
