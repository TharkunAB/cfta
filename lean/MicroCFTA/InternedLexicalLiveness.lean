import MicroCFTA.InternedFreeAbsenceContext

/-!
# Source child liveness from abstract lexical inputs

A literal-name map can identify unrelated lexical inputs. It cannot change
which child results are empty. The pure profile interpreter therefore gives
the actual source edge-selection test before names are instantiated.
-/
namespace MicroCFTA.InternedLexicalLiveness
open InternedConstructorTemplates InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedProbeProvenance InternedRootProfile InternedProfileSemantics InternedProfileComposition
open InternedFreeAbsenceContext
open InternedBinderProtocol (Reference)

/-- Actual completed child results have exactly the abstract lexical empty-child decision. -/
theorem buildMany_empty [DecidableEq (EdgeKey Symbol Guard)] {Atom : Type}
    (expressions : List (Syntax Symbol Guard)) (atoms : List Atom) (names : Atom → Reference)
    (state final : State Symbol Guard) (context : Context state (atoms.map names))
    (values : List (Value Symbol Guard))
    (completed : buildMany expressions ((atoms.map names).map Value.reference) state = .done values final) :
    values.any (fun child => child.referenceOf == .empty) =
      !(evaluateMany expressions (atoms.map (fun atom => some [atom]))).all (fun value => !isEmpty value) := by
  have matched := (InternedNestedProfiles.buildMany_profile expressions _ state context.normal
    context.inputs context.profiles).result values final completed
  have finalContext : Context final (atoms.map names) := by
    simpa only [completed, Outcome.state] using context.many expressions
  have available := (buildMany_verified expressions _ state context.normal.facts context.inputs).result values final completed
  have actual : values.all (fun child => !isEmpty (profile child)) =
      (evaluateMany expressions (atoms.map (fun atom => some [atom]))).all (fun value => !isEmpty value) := by
    have evaluated : evaluateMany expressions (((atoms.map names).map (Value.reference (Symbol := Symbol) (Guard := Guard))).map profile) =
        (evaluateMany expressions (atoms.map (fun atom => some [atom]))).map (mapNames names) := by
      rw [← evaluateMany_map names]
      congr 1
      simp [List.map_map, Function.comp_def, mapNames, profile]
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

end MicroCFTA.InternedLexicalLiveness
