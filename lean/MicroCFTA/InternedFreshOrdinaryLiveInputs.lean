import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedFreshOrdinaryActiveOrigins
import MicroCFTA.InternedFreeNameSemantics

/-!
# Live varying references beside arbitrary fixed captured values

A lexical slot contains a fixed value or a varying reference.
Both executions retain the same fixed values. The existing pure profile
interpreter selects the surviving edges. Free labels track only varying
slots. Names inside fixed profiles remain constant in both executions.
-/
namespace MicroCFTA.InternedFreshOrdinaryLiveInputs
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryContext
open InternedRootProfile (profile)
open InternedProfileSemantics (Abstract mapNames)
open InternedBinderProtocol (Reference)

/-- Instantiate a varying reference and retain each fixed captured record exactly. -/
def input (names : Atom → Reference) : Sum (Value Symbol Guard) Atom → Value Symbol Guard
  | .inl value => value
  | .inr atom => .reference (names atom)

/-- A symbolic profile retains fixed reference names and distinguishes every varying slot. -/
def inputProfile : Sum (Value Symbol Guard) Atom → Abstract (Sum Reference Atom)
  | .inl value => mapNames Sum.inl (profile value)
  | .inr atom => some [.inr atom]

/-- Only varying slots need an agreement premise. Fixed records are identical. -/
def inputNames : Sum (Value Symbol Guard) Atom → List (Sum Reference Atom)
  | .inl _ => []
  | .inr atom => [.inr atom]

/-- Interpret the surviving varying inputs with the actual fixed input profiles. -/
def liveInputs (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) : List (Sum Reference Atom) :=
  InternedFreeNameSemantics.evaluate expression (inputs.map inputProfile) (inputs.map inputNames)

/-- Instantiation leaves fixed profile names unchanged. -/
theorem input_profile (names : Atom → Reference) (selected : Sum (Value Symbol Guard) Atom) :
    profile (input names selected) = mapNames (Sum.elim id names) (inputProfile selected) := by
  cases selected with
  | inl value => cases current : profile value <;> simp [input, inputProfile, current, mapNames, List.map_map, Function.comp_def]
  | inr atom => simp [input, inputProfile, profile, mapNames]

/-- All actual input profiles are instances of one common symbolic profile list. -/
theorem input_profiles (names : Atom → Reference) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    (inputs.map (input names)).map profile =
      (inputs.map inputProfile).map (mapNames (Sum.elim id names)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro selected member
  exact input_profile names selected

/-- Lifting lexical variables leaves fixed captured values unchanged. -/
def liftInput : Sum (Value Symbol Guard) Atom → Sum (Value Symbol Guard) (Sum Unit Atom)
  | .inl value => .inl value
  | .inr atom => .inr (.inr atom)

/-- Reassociate the new local label while retaining every fixed reference name. -/
def liftName : Sum Unit (Sum Reference Atom) → Sum Reference (Sum Unit Atom)
  | .inl bound => .inr (.inl bound)
  | .inr (.inl name) => .inl name
  | .inr (.inr atom) => .inr (.inr atom)

/-- A lifted captured slot has the same symbolic profile after label reassociation. -/
theorem lift_profile (selected : Sum (Value Symbol Guard) Atom) :
    inputProfile (liftInput selected) = mapNames liftName (mapNames Sum.inr (inputProfile selected)) := by
  cases selected with
  | inl value => cases current : profile value <;> simp [liftInput, inputProfile, current, mapNames, liftName, List.map_map, Function.comp_def]
  | inr atom => simp [inputProfile, liftInput, mapNames, liftName]

/-- A lifted captured slot retains its varying-name label after reassociation. -/
theorem lift_names (selected : Sum (Value Symbol Guard) Atom) :
    inputNames (liftInput selected) = (inputNames selected).map (fun name => liftName (.inr name)) := by
  cases selected <;> rfl

/-- The local input followed by lifted captures has exactly the original instantiated values. -/
theorem local_inputs (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference) (name : Reference) :
    (.inr (.inl ()) :: inputs.map liftInput).map (input (Sum.elim (fun _ => name) names)) =
      .reference name :: inputs.map (input names) := by
  simp only [List.map_cons, List.map_map, input, Sum.elim_inl]
  congr 1
  apply List.map_congr_left
  intro selected member
  cases selected <;> rfl

/-- The actual binder body support is the original symbolic body with reassociated labels. -/
theorem body_inputs (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    liveInputs expression (.inr (.inl ()) :: inputs.map liftInput) =
      (InternedFreeNameSemantics.evaluate expression
        (some [.inl ()] :: (inputs.map inputProfile).map (mapNames Sum.inr))
        ([.inl ()] :: (inputs.map inputNames).map (List.map Sum.inr))).map liftName := by
  rw [liveInputs, ← InternedFreeNameSemantics.evaluate_map liftName]
  congr 1
  · simp only [List.map_cons, List.map_map, inputProfile, mapNames, Option.map_some, List.map_cons, List.map_nil, liftName]
    congr 1
    apply List.map_congr_left
    intro selected member
    exact lift_profile selected
  · simp only [List.map_cons, List.map_map, inputNames, List.map_cons, List.map_nil, liftName]
    congr 1
    apply List.map_congr_left
    intro selected member
    simpa only [List.map_map, Function.comp_def] using lift_names selected

/-- Supplying the same local reference retains agreement on every live varying capture. -/
theorem callback_agreement (expression : Syntax Symbol Guard) (smart : Bool)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference) (name : Reference)
    (agree : ∀ label ∈ liveInputs (.binder smart expression) inputs,
      Sum.elim id firstNames label = Sum.elim id secondNames label) :
    ∀ label ∈ liveInputs expression (.inr (.inl ()) :: inputs.map liftInput),
      Sum.elim id (Sum.elim (fun _ => name) firstNames) label =
        Sum.elim id (Sum.elim (fun _ => name) secondNames) label := by
  intro label member
  cases label with
  | inl fixed => rfl
  | inr selected =>
      cases selected with
      | inl bound => rfl
      | inr atom =>
          apply agree (.inr atom)
          rw [liveInputs, InternedFreeNameSemantics.evaluate, InternedFreeNameSemantics.lower_member]
          rw [body_inputs] at member
          obtain ⟨original, included, same⟩ := List.mem_map.mp member
          cases original with
          | inl bound => cases same
          | inr external =>
              cases external with
              | inl fixed => cases same
              | inr old => cases same; exact included

end MicroCFTA.InternedFreshOrdinaryLiveInputs
