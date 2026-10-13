import MicroCFTA.InternedFreeNameSemantics
import MicroCFTA.InternedProfileCallbackForm

/-!
# Fixed captures and an optional argument for free names

One symbolic body execution determines the free names in every concrete
body call. The supplied argument can equal a captured name. Both binder
forms retain exactly the symbolic captures.
-/
namespace MicroCFTA.InternedFreeNameForm
open InternedNestedConstruction InternedRootProfile
open InternedProfileSemantics (mapNames)
open InternedProfileCallbackForm (supply captures usesArgument)
open InternedFreeNameSemantics
open InternedBinderProtocol (Reference)

/-- Execute a body with a symbolic argument distinct from all captured names. -/
def symbolic (body : Syntax Symbol Guard) (profiles : List Profile)
    (freeNames : List (List Reference)) : List (Sum Unit Reference) :=
  evaluate body (some [.inl ()] :: profiles.map (mapNames Sum.inr))
    ([.inl ()] :: freeNames.map (List.map Sum.inr))

/-- Substitution of any reference commutes with the full free-name interpreter. -/
theorem evaluate_supplied (body : Syntax Symbol Guard) (profiles : List Profile)
    (freeNames : List (List Reference)) (argument : Reference) :
    evaluate body (some [argument] :: profiles) ([argument] :: freeNames) =
      (symbolic body profiles freeNames).map (supply argument) := by
  have mapped := evaluate_map (supply argument) body
    (some [.inl ()] :: profiles.map (mapNames Sum.inr))
    ([.inl ()] :: freeNames.map (List.map Sum.inr))
  have profileInputs : (some [Sum.inl ()] :: profiles.map (mapNames Sum.inr)).map
      (mapNames (supply argument)) = some [argument] :: profiles := by
    simp [mapNames, supply, List.map_map, Function.comp_def]
  have freeInputs : ([Sum.inl ()] :: freeNames.map (List.map Sum.inr)).map
      (List.map (supply argument)) = [argument] :: freeNames := by
    simp [supply, List.map_map, Function.comp_def]
  simpa only [profileInputs, freeInputs, symbolic] using mapped

/-- Every concrete body free name is a fixed capture or the supplied argument. -/
theorem supplied_member (body : Syntax Symbol Guard) (profiles : List Profile)
    (freeNames : List (List Reference)) (argument name : Reference) :
    name ∈ evaluate body (some [argument] :: profiles) ([argument] :: freeNames) ↔
      name ∈ captures (symbolic body profiles freeNames) ∨
        (usesArgument (symbolic body profiles freeNames) = true ∧ name = argument) := by
  rw [evaluate_supplied]
  exact InternedProfileCallbackForm.supplied_member _ argument name

/-- Every name other than the supplied argument occurs exactly when it is a fixed capture. -/
theorem supplied_other (body : Syntax Symbol Guard) (profiles : List Profile)
    (freeNames : List (List Reference)) (argument name : Reference) (different : name ≠ argument) :
    name ∈ evaluate body (some [argument] :: profiles) ([argument] :: freeNames) ↔
      name ∈ captures (symbolic body profiles freeNames) := by
  simp only [supplied_member, different, and_false, or_false]

/-- Raw and smart binders both retain exactly the symbolic captured free names. -/
theorem binder_captures (smart : Bool) (body : Syntax Symbol Guard)
    (profiles : List Profile) (freeNames : List (List Reference)) :
    evaluate (.binder smart body) profiles freeNames = captures (symbolic body profiles freeNames) := by
  rw [evaluate]
  simp only [lower, captures, symbolic]
  congr 1
  funext name
  cases name <;> rfl

/-- Every full body has one fixed captured set and one optional argument contribution. -/
theorem callback_form (body : Syntax Symbol Guard) (profiles : List Profile)
    (freeNames : List (List Reference)) :
    ∃ captured uses, ∀ argument name,
      name ∈ evaluate body (some [argument] :: profiles) ([argument] :: freeNames) ↔
        name ∈ response captured uses argument := by
  refine ⟨captures (symbolic body profiles freeNames), usesArgument (symbolic body profiles freeNames), ?_⟩
  intro argument name
  rw [supplied_member, InternedProfileCallbackForm.response_member]

/-- Every fixed body capture comes from one supplied free-name list. -/
theorem captures_origins (body : Syntax Symbol Guard) (profiles : List Profile)
    (freeNames : List (List Reference)) (name : Reference)
    (member : name ∈ captures (symbolic body profiles freeNames)) :
    ∃ names ∈ freeNames, name ∈ names := by
  rw [← binder_captures true body profiles freeNames] at member
  exact evaluate_origins (.binder true body) profiles freeNames name member

end MicroCFTA.InternedFreeNameForm
