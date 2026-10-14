import MicroCFTA.InternedFreshOrdinaryLiveInputs
import MicroCFTA.InternedProfileComposition
import MicroCFTA.InternedRootProfileNode
import MicroCFTA.InternedLiteralObservations

/-!
# Actual child liveness with fixed captured records

The common symbolic profiles determine the actual empty-child test.
Both executions can vary their literal references while retaining arbitrary
fixed captured records. No caller supplies an edge-selection agreement.
-/
namespace MicroCFTA.InternedFreshOrdinaryLexicalLiveness
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedRootProfile InternedProfileSemantics InternedProfileComposition
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedBinderProtocol (Reference)

/-- Actual completed child results have exactly the abstract lexical empty-child decision. -/
theorem buildMany_empty [DecidableEq (EdgeKey Symbol Guard)] {Atom : Type}
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (state final : State Symbol Guard) (context : Context state (inputs.map (input names)))
    (values : List (Value Symbol Guard))
    (completed : buildMany expressions (inputs.map (input names)) state = .done values final) :
    values.any (fun child => child.referenceOf == .empty) =
      !(evaluateMany expressions (inputs.map inputProfile)).all (fun value => !isEmpty value) := by
  have matched := (InternedFreshOrdinaryProfiles.buildMany_profile expressions _ state context.normal
    context.inputs context.profiles).result values final completed
  have finalContext : Context final (inputs.map (input names)) := by
    simpa only [completed, Outcome.state] using context.many expressions
  have available := (buildMany_verified expressions _ state context.normal.facts context.inputs).result values final completed
  have actual : values.all (fun child => !isEmpty (profile child)) =
      (evaluateMany expressions (inputs.map inputProfile)).all (fun value => !isEmpty value) := by
    have evaluated : evaluateMany expressions ((inputs.map (input names)).map profile) =
        (evaluateMany expressions (inputs.map inputProfile)).map (mapNames (Sum.elim id names)) := by
      rw [input_profiles, evaluateMany_map]
    simpa only [evaluated, List.all_map, Function.comp_def, isEmpty_map] using children_matched matched
  rw [← actual]
  have tests : ∀ value ∈ values, (value.referenceOf == .empty) = isEmpty (profile value) := by
    intro value member
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, InternedLiteralObservations.empty_test,
      InternedRootProfileNode.profile_empty_iff value final finalContext.normal.proper (available value member),
      InternedEmptyNormalization.reference_empty]
  rw [← List.any_eq_not_all_not]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  apply exists_congr
  intro value
  apply and_congr_right
  intro member
  rw [tests value member]

end MicroCFTA.InternedFreshOrdinaryLexicalLiveness
