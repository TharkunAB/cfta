import MicroCFTA.SourceCurrentNativeNormalizedComparison

/-!
# Finite varying-label support for normalized source comparison

The label list covers the varying lexical slots. Names assigned to labels
outside that list need no freshness or absence condition.
-/
namespace MicroCFTA.SourceCurrentNativeNormalizedComparisonFinite
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedDeepFreeDepth InternedDepthSemantics
open SourceCurrentNativeNormalizedComparison
open InternedBinderProtocol (Reference)
variable {Atom : Type}

/-- Every surviving varying label comes from an actual varying lexical slot. -/
theorem support_varying_member (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atom : Atom)
    (member : .inr atom ∈ SourceCurrentNativeNormalizationInputs.support expression inputs) :
    .inr atom ∈ inputs := by
  obtain ⟨names, supplied, included⟩ := InternedFreeNameSemantics.evaluate_origins expression
    (inputs.map inputProfile) (inputs.map SourceCurrentNativeNormalizationInputs.inputNames) (.inr atom) member
  obtain ⟨selected, present, same⟩ := List.mem_map.mp supplied
  rw [← same] at included
  cases selected with
  | inl value =>
      obtain ⟨_, _, impossible⟩ := List.mem_map.mp included
      cases impossible
  | inr original =>
      have equal : atom = original := Sum.inr.inj (List.mem_singleton.mp included)
      exact equal ▸ present

/-- Finite slot coverage transports deep-name absence without assumptions on other labels. -/
theorem deep_transport_on [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (atoms : List Atom) (firstNames secondNames : Atom → Reference)
    (before after later final : State Symbol Guard)
    (context : Context before (inputs.map (input firstNames)))
    (laterContext : Context later (inputs.map (input secondNames)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (laterHeap : InternedFreshOrdinaryDepthHeap.Heap later)
    (first second : Value Symbol Guard)
    (firstActual : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondActual : build expression (inputs.map (input secondNames)) later = .done second final)
    (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms)
    (absent : ∀ atom ∈ atoms, firstNames atom ∉ deepNames first)
    (fresh : ∀ atom ∈ atoms,
      .inl (secondNames atom) ∉ SourceCurrentNativeNormalizationInputs.support expression inputs) :
    ∀ atom ∈ atoms, secondNames atom ∉ deepNames second := by
  intro atom selected member
  obtain ⟨label, present, same⟩ := List.mem_map.mp
    ((actual_deep expression inputs secondNames later final laterContext laterHeap second secondActual _).mp member)
  cases label with
  | inl fixed =>
      have supported := (symbolic_free_support expression inputs firstNames before context (.inl fixed)).mp
        (List.mem_append_right _ present)
      exact fresh atom selected (same ▸ supported)
  | inr varied =>
      have supported := (symbolic_free_support expression inputs firstNames before context (.inr varied)).mp
        (List.mem_append_right _ present)
      have included := covered varied (support_varying_member expression inputs varied supported)
      exact absent varied included
        ((actual_deep expression inputs firstNames before after context heap first firstActual _).mpr
          (List.mem_map.mpr ⟨.inr varied, present, rfl⟩))

/-- Entering a body requires freshness only for its explicit extended finite label list. -/
theorem extend_fresh_on (body : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (names : Atom → Reference) (argument : Reference)
    (outer : ∀ atom ∈ atoms,
      .inl (names atom) ∉ SourceCurrentNativeNormalizationInputs.support (.binder true body) inputs)
    (localFresh : .inl argument ∉ SourceCurrentNativeNormalizationInputs.support (.binder true body) inputs) :
    ∀ atom ∈ (.inl () :: atoms.map Sum.inr),
      .inl (Sum.elim (fun _ => argument) names atom) ∉
        SourceCurrentNativeNormalizationInputs.support body (.inr (.inl ()) :: inputs.map liftInput) := by
  intro atom selected member
  cases atom with
  | inl token =>
      exact localFresh ((capture_support body inputs (.inl argument)).mp member)
  | inr atom =>
      have included : atom ∈ atoms := by
        rcases List.mem_cons.mp selected with impossible | selected
        · cases impossible
        · obtain ⟨original, included, same⟩ := List.mem_map.mp selected
          exact (Sum.inr.inj same) ▸ included
      exact outer atom included ((capture_support body inputs (.inl (names atom))).mp member)

end MicroCFTA.SourceCurrentNativeNormalizedComparisonFinite
