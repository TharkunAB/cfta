import MicroCFTA.SourceCurrentUsedBinderAliasTransport
import MicroCFTA.InternedActualProbeTags
import MicroCFTA.InternedRecordDepthCompletion
import MicroCFTA.SourceCurrentUsedBinderRootAlternatives
import MicroCFTA.SourceCurrentStoredReconstruction

/-!
# Actual source output tags through live lexical aliases

Full source execution reflects empty and bare-reference output tags.
Nested source binders and captured Depth aliases remain in scope.
The callback induction step constructs its actual calls. Its comparison
uses an explicit strict source-body induction hypothesis.
-/
namespace MicroCFTA.SourceCurrentUsedBinderOutputTags
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryLiveInputs (input inputProfile input_profiles liftInput liftName local_inputs)
open SourceCurrentNativeNormalizationInputs (support)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open InternedRootProfile (profile Single)
open InternedBinderProtocol (Reference)
variable {Atom : Type}

private def rootProfile (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :=
  InternedProfileSemantics.evaluate expression (inputs.map inputProfile)

private theorem shape_profiles (inputs : List (Sum (Value Symbol Guard) Atom)) :
    (inputs.map SourceCurrentNativeNormalizedComparison.inputShape).map InternedDepthSemanticProjections.profile =
      inputs.map inputProfile := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro selected member
  cases selected with
  | inl value =>
      exact (InternedDepthSemanticProjections.profile_map Sum.inl (InternedRecordDepthShape.shape value)).trans
        (congrArg (InternedProfileSemantics.mapNames Sum.inl) (InternedRecordDepthShape.shape_profile value))
  | inr atom => rfl

private theorem coherent_shapes (inputs : List (Sum (Value Symbol Guard) Atom)) :
    InternedDepthSemanticProjections.CoherentMany (inputs.map SourceCurrentNativeNormalizedComparison.inputShape) := by
  intro value member
  obtain ⟨selected, present, rfl⟩ := List.mem_map.mp member
  cases selected with
  | inl value => exact InternedDepthSemanticProjections.coherent_map Sum.inl _ (InternedRecordDepthShape.shape_coherent value)
  | inr atom => intro _; rfl

private theorem root_scoped (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before : State Symbol Guard) (context : Context before (inputs.map (input names)))
    (label : Sum Reference Atom) (member : label ∈ (rootProfile expression inputs).getD []) :
    label ∈ Scope expression inputs := by
  have projected : InternedDepthSemanticProjections.profile
      (SourceCurrentNativeNormalizedComparison.symbolic expression inputs) = rootProfile expression inputs := by
    rw [SourceCurrentNativeNormalizedComparison.symbolic,
      InternedDepthSemanticProjections.evaluate_profile expression _ (coherent_shapes inputs), shape_profiles]
    rfl
  rw [← projected, InternedDepthSemanticProjections.profile] at member
  have root : label ∈ (SourceCurrentNativeNormalizedComparison.symbolic expression inputs).roots := by
    split at member
    · simp only [Option.getD_none, List.not_mem_nil] at member
    · exact member
  apply List.mem_cons_of_mem
  apply (SourceCurrentNativeNormalizedComparison.symbolic_free_support expression inputs names before context label).mp
  exact List.mem_append_left _ root

private theorem output_profile [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after) :
    InternedRootProfile.Equivalent (profile value)
      (InternedProfileSemantics.mapNames (Sum.elim id names) (rootProfile expression inputs)) := by
  have observed := (InternedFreshOrdinaryProfiles.build_profile expression _ before context.normal context.inputs context.profiles).result
    value after actual
  rw [input_profiles, InternedProfileSemantics.evaluate_map] at observed
  exact observed

private theorem output_context [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before after : State Symbol Guard) (context : Context before environment) (value : Value Symbol Guard)
    (actual : build expression environment before = .done value after) :
    Context after environment ∧ Available after value := by
  exact ⟨by simpa only [actual, Outcome.state] using context.build expression,
    (build_verified expression environment before context.normal.facts context.inputs).result value after actual⟩

private theorem single_map (labels : List (Sum Reference Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (aliases : ∀ label ∈ labels,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) :
    Single firstOwn (labels.map (Sum.elim id firstNames)) ↔
      Single secondOwn (labels.map (Sum.elim id secondNames)) := by
  constructor
  · rintro ⟨member, unique⟩
    obtain ⟨label, present, same⟩ := List.mem_map.mp member
    refine ⟨List.mem_map.mpr ⟨label, present, (aliases label present).mp same⟩, ?_⟩
    intro name member
    obtain ⟨other, included, rfl⟩ := List.mem_map.mp member
    exact (aliases other included).mp (unique _ (List.mem_map.mpr ⟨other, included, rfl⟩))
  · rintro ⟨member, unique⟩
    obtain ⟨label, present, same⟩ := List.mem_map.mp member
    refine ⟨List.mem_map.mpr ⟨label, present, (aliases label present).mpr same⟩, ?_⟩
    intro name member
    obtain ⟨other, included, rfl⟩ := List.mem_map.mp member
    exact (aliases other included).mpr (unique _ (List.mem_map.mpr ⟨other, included, rfl⟩))

/-- Equal live alias tests reflect the exact bare-reference tag of both actual outputs. -/
theorem bare [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final)
    (aliases : ∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) :
    first = .reference firstOwn ↔ second = .reference secondOwn := by
  have firstProfile := output_profile expression inputs firstNames before after firstContext first firstDone
  have secondProfile := output_profile expression inputs secondNames later final secondContext second secondDone
  have firstOutput := output_context expression _ before after firstContext first firstDone
  have secondOutput := output_context expression _ later final secondContext second secondDone
  rw [← InternedRootProfileReflection.profile_single_iff first after firstOutput.1.normal firstOutput.2 firstOwn,
    ← InternedRootProfileReflection.profile_single_iff second final secondOutput.1.normal secondOutput.2 secondOwn,
    InternedActualProbeTags.single_equivalent firstOwn firstProfile,
    InternedActualProbeTags.single_equivalent secondOwn secondProfile]
  cases computed : rootProfile expression inputs with
  | none => simp only [InternedProfileSemantics.mapNames, computed, Option.map_none, Option.getD_none, Single, List.not_mem_nil, false_and]
  | some labels =>
      simp only [InternedProfileSemantics.mapNames, computed, Option.map_some, Option.getD_some]
      apply single_map labels firstNames secondNames firstOwn secondOwn
      intro label member
      exact aliases label (root_scoped expression inputs firstNames before firstContext label (by simpa only [computed] using member))

/-- A scoped lexical label needs only the existing live alias relation. -/
theorem scoped_bare [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (label : Sum Reference Atom)
    (member : label ∈ Scope expression inputs) (aliases : Aliases expression inputs firstNames secondNames)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final) :
    first = .reference (Sum.elim id firstNames label) ↔ second = .reference (Sum.elim id secondNames label) :=
  bare expression inputs firstNames secondNames _ _ before after later final firstContext secondContext
    first second firstDone secondDone (fun other present => aliases other present label member)

/-- Captured aliases with Depth preserve exact bare Depth outputs. -/
theorem depth_bare [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (aliases : Aliases expression inputs firstNames secondNames)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final) :
    first = .reference .depth ↔ second = .reference .depth :=
  scoped_bare expression inputs firstNames secondNames (.inl .depth) List.mem_cons_self aliases
    before after later final firstContext secondContext first second firstDone secondDone

/-- Source empty outputs agree under arbitrary assignments, with no freshness premise. -/
theorem empty [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final) :
    first = .empty ↔ second = .empty := by
  have firstProfile := output_profile expression inputs firstNames before after firstContext first firstDone
  have secondProfile := output_profile expression inputs secondNames later final secondContext second secondDone
  have firstOutput := output_context expression _ before after firstContext first firstDone
  have secondOutput := output_context expression _ later final secondContext second secondDone
  rw [← InternedRootProfileNode.profile_empty_iff first after firstOutput.1.normal.proper firstOutput.2,
    ← InternedRootProfileNode.profile_empty_iff second final secondOutput.1.normal.proper secondOutput.2,
    InternedProfileComposition.empty_same firstProfile, InternedProfileComposition.empty_same secondProfile]
  cases computed : rootProfile expression inputs with
  | none => simp only [InternedProfileSemantics.mapNames, computed, Option.map_none, reduceCtorEq]
  | some labels => simp only [InternedProfileSemantics.mapNames, computed, Option.map_some, Option.some.injEq, List.map_eq_nil_iff]

end MicroCFTA.SourceCurrentUsedBinderOutputTags
