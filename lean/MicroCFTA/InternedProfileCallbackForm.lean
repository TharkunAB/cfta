import MicroCFTA.InternedProfileSemantics
import MicroCFTA.InternedTwoProbeProfiles

/-!
# A syntax-derived form for arbitrary callback root profiles

One symbolic execution marks the supplied argument separately from fixed
captured reference names. The map law then derives every concrete call.
No binder-free restriction or assumed callback equation is used in this
pure interpretation. Source record correspondence remains separate.
-/
namespace MicroCFTA.InternedProfileCallbackForm
open InternedNestedConstruction InternedProfileSemantics InternedRootProfile
open InternedBinderProtocol (Reference)

/-- Substitute the callback argument while leaving each captured name unchanged. -/
def supply (name : Reference) : Sum Unit Reference → Reference
  | .inl _ => name
  | .inr captured => captured

/-- Extract the captured names from a symbolic result. -/
def captures (names : List (Sum Unit Reference)) : List Reference :=
  names.filterMap (fun name => match name with | .inl _ => none | .inr captured => some captured)

/-- Record whether the symbolic result contains the supplied callback argument. -/
def usesArgument (names : List (Sum Unit Reference)) : Bool :=
  names.any (fun name => match name with | .inl _ => true | .inr _ => false)

/-- One symbolic execution determines the form of every reference-parameterized body call. -/
def symbolic (body : Syntax Symbol Guard) (environment : List Profile) : Abstract (Sum Unit Reference) :=
  evaluate body (some [.inl ()] :: environment.map (mapNames Sum.inr))

/-- Concrete argument substitution commutes with the complete pure syntax interpreter. -/
theorem evaluate_supplied (body : Syntax Symbol Guard) (environment : List Profile) (name : Reference) :
    evaluate body (some [name] :: environment) = mapNames (supply name) (symbolic body environment) := by
  have mapped := evaluate_map (supply name) body (some [.inl ()] :: environment.map (mapNames Sum.inr))
  have inputs : (some [Sum.inl ()] :: environment.map (mapNames Sum.inr)).map (mapNames (supply name)) =
      some [name] :: environment := by
    simp [mapNames, supply, List.map_map, Function.comp_def]
  simpa only [inputs, symbolic] using mapped

/-- Every concrete root reference comes from a fixed capture or the supplied argument. -/
theorem supplied_member (names : List (Sum Unit Reference)) (argument name : Reference) :
    name ∈ names.map (supply argument) ↔ name ∈ captures names ∨ (usesArgument names = true ∧ name = argument) := by
  induction names with
  | nil => simp [captures, usesArgument]
  | cons first rest ih =>
      cases first with
      | inl token =>
          cases token
          by_cases same : name = argument <;> simp [captures, usesArgument, supply, ih, same]
      | inr captured => simp [captures, usesArgument, supply, ih, or_assoc]

/-- The source response list has the same captured-or-argument membership rule. -/
theorem response_member (captured : List Reference) (uses : Bool) (argument name : Reference) :
    name ∈ response captured uses argument ↔ name ∈ captured ∨ (uses = true ∧ name = argument) := by
  cases uses <;> simp [response]

/-- A pure symbolic result derives its concrete captured-plus-argument profile. -/
theorem pure_form (body : Syntax Symbol Guard) (environment : List Profile) (names : List (Sum Unit Reference))
    (computed : symbolic body environment = some names) (argument : Reference) :
    Equivalent (evaluate body (some [argument] :: environment)) (some (response (captures names) (usesArgument names) argument)) := by
  rw [evaluate_supplied, computed]
  constructor
  · simp [mapNames]
  · intro name
    simpa only [mapNames, Option.map_some, Option.getD_some, response_member] using supplied_member names argument name

/-- An opaque symbolic result stays opaque at every concrete supplied reference. -/
theorem opaque_form (body : Syntax Symbol Guard) (environment : List Profile)
    (computed : symbolic body environment = none) (argument : Reference) :
    evaluate body (some [argument] :: environment) = none := by
  rw [evaluate_supplied, computed]
  rfl

/-- Every complete source expression has one of these two argument-independent profile forms in the pure model. -/
theorem callback_form (body : Syntax Symbol Guard) (environment : List Profile) :
    (∀ argument, evaluate body (some [argument] :: environment) = none) ∨
      ∃ captured uses, ∀ argument,
        Equivalent (evaluate body (some [argument] :: environment)) (some (response captured uses argument)) := by
  cases computed : symbolic body environment with
  | none => exact Or.inl (opaque_form body environment computed)
  | some names => exact Or.inr ⟨captures names, usesArgument names, pure_form body environment names computed⟩

end MicroCFTA.InternedProfileCallbackForm
