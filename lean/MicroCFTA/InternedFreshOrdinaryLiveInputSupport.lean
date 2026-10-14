import MicroCFTA.InternedFreshOrdinaryLiveInputReadiness
import MicroCFTA.InternedFreeNameInputSubset

/-!
# Actual free names expose every live varying input

The symbolic support omits names inside fixed records. Adding those names
preserves every varying input observation. Actual repaired callbacks expose
the resulting capture away from their supplied argument.
-/
namespace MicroCFTA.InternedFreshOrdinaryLiveInputSupport
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedFreeNameSemantics InternedRootProfile
open InternedBinderProtocol (Reference)

/-- Each live varying label comes from an actual varying lexical slot. -/
theorem live_member (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (atom : Atom) (member : .inr atom ∈ liveInputs expression inputs) : .inr atom ∈ inputs := by
  obtain ⟨names, supplied, included⟩ := evaluate_origins expression (inputs.map inputProfile)
    (inputs.map inputNames) (.inr atom) member
  obtain ⟨selected, present, same⟩ := List.mem_map.mp supplied
  rw [← same] at included
  cases selected with
  | inl value => cases included
  | inr original =>
      have equal : atom = original := Sum.inr.inj (List.mem_singleton.mp included)
      exact equal ▸ present

/-- Every symbolic varying-name input occurs in the corresponding actual free-name input. -/
theorem input_names_included (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (index : Nat) (name : Reference)
    (member : name ∈ (((inputs.map inputNames).map (List.map (Sum.elim id names)))[index]?).getD []) :
    name ∈ ((((inputs.map (input names)).map Value.free)[index]?).getD []) := by
  cases found : inputs[index]? with
  | none => simp [List.getElem?_map, found] at member
  | some selected =>
      cases selected with
      | inl value => simp [List.getElem?_map, found, inputNames] at member
      | inr atom => simpa [List.getElem?_map, found, input, Value.free, inputNames] using member

/-- Each live varying input occurs in the full actual free-name interpretation. -/
theorem live_free (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (label : Sum Reference Atom) (member : label ∈ liveInputs expression inputs) :
    Sum.elim id names label ∈ evaluate expression ((inputs.map (input names)).map profile)
      ((inputs.map (input names)).map Value.free) := by
  have mapped : Sum.elim id names label ∈ (liveInputs expression inputs).map (Sum.elim id names) :=
    List.mem_map.mpr ⟨label, member, rfl⟩
  rw [liveInputs, ← evaluate_map] at mapped
  have included := InternedFreeNameInputSubset.evaluate_included expression _ _ _
    (input_names_included inputs names) _ mapped
  simpa only [← input_profiles names inputs] using included

/-- An actual repaired callback exposes every live varying capture other than its supplied name. -/
theorem callback_live [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (argument : Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (available : Available before (.reference argument)) (value : Value Symbol Guard)
    (done : callback body (inputs.map (input names)) argument before = .done value after)
    (label : Sum Reference Atom) (live : label ∈ liveInputs (.binder smart body) inputs)
    (different : Sum.elim id names label ≠ argument) : Sum.elim id names label ∈ value.free := by
  have captured := live_free (.binder smart body) inputs names label live
  rw [InternedFreeNameForm.binder_captures] at captured
  exact (InternedFreshOrdinarySourceFreeNames.callback_other body _ argument before context.normal
    (context.local argument available).inputs context.freeNames context.profiles value after done _ different).mpr captured

end MicroCFTA.InternedFreshOrdinaryLiveInputSupport
