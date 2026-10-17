import MicroCFTA.SourceCurrentNativeNormalizedComparisonFinite
import MicroCFTA.InternedFreshOrdinaryLiveInputReplay

/-!
# Inactive varying slots in actual normalized comparison

If no varying slot occurs in the source support, the two actual complete
executions return the same record. Fresh fixed support then makes both
root erasures leave that record unchanged.
-/
namespace MicroCFTA.SourceCurrentNativeNormalizedComparisonInactive
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedBinderProtocol (Reference)
open SourceCurrentNativeNormalizedComparison SourceCurrentNativeStrippedAlternatives
open SourceCurrentNativeNormalizationInputs (support)
variable {Atom : Type}

/-- Every live lexical label also occurs in the full fixed and varying support. -/
theorem live_support (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (label : Sum Reference Atom)
    (member : label ∈ liveInputs expression inputs) : label ∈ support expression inputs := by
  apply InternedFreeNameInputSubset.evaluate_included expression _ _ _ _ label member
  intro index name included
  cases found : inputs[index]? with
  | none => simp [List.getElem?_map, found] at included
  | some selected =>
      cases selected with
      | inl value => simp [List.getElem?_map, found, inputNames] at included
      | inr atom => simpa [List.getElem?_map, found, inputNames,
          SourceCurrentNativeNormalizationInputs.inputNames] using included

/-- Removing names absent from a record's free names leaves its root alternatives unchanged. -/
theorem strip_absent (names : List Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (available : Available state value) (absent : ∀ name ∈ names, name ∉ value.free) :
    stripMany names (unionMembers value) = unionMembers value := by
  have kept (name : Reference) (selected : name ∈ names) :
      InternedRootAlternativeLists.remove name (unionMembers value) = unionMembers value := by
    apply List.filter_eq_self.mpr
    intro alternative member
    apply bne_iff_ne.mpr
    intro same
    have equality := (referenceOf_self_iff name alternative).mp same
    have root : Value.reference name ∈ unionMembers value := equality ▸ member
    have free := (InternedNormalizationFree.unionMembers_free state normal.facts.coherent value available name).mpr
      ⟨.reference name, root, by simp only [Value.free, List.mem_singleton]⟩
    exact absent name selected free
  induction names with
  | nil => rfl
  | cons name names ih =>
      rw [stripMany, kept name List.mem_cons_self]
      apply ih
      · intro own selected
        exact absent own (List.mem_cons_of_mem name selected)
      · intro own selected
        exact kept own (List.mem_cons_of_mem name selected)

/-- Dead varying slots compare without any stored Mu comparison premise. -/
theorem inactive_compared [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (atoms : List Atom) (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal common)
    (inactive : ∀ atom, .inr atom ∉ support expression inputs) :
    Compared expression inputs atoms firstNames secondNames common := by
  intro before later after final context laterContext _heap _laterHeap first second
    firstActual secondActual growth laterGrowth _history _laterHistory firstFresh secondFresh _shallow
  have equal := InternedFreshOrdinaryLiveInputReplay.build_same expression inputs firstNames secondNames
    (by
      intro label live
      cases label with
      | inl fixed => rfl
      | inr atom => exact False.elim (inactive atom (live_support expression inputs (.inr atom) live)))
    before later common after final context laterContext normal.facts.coherent first second
    firstActual secondActual growth laterGrowth
  have firstContext : Context after (inputs.map (input firstNames)) := by
    simpa only [firstActual, Outcome.state] using context.build expression
  have secondContext : Context final (inputs.map (input secondNames)) := by
    simpa only [secondActual, Outcome.state] using laterContext.build expression
  have firstAvailable := (build_verified expression _ before context.normal.facts context.inputs).result _ _ firstActual
  have secondAvailable := (build_verified expression _ later laterContext.normal.facts laterContext.inputs).result _ _ secondActual
  have firstAbsent : ∀ name ∈ atoms.map firstNames, name ∉ first.free := by
    intro name member named
    obtain ⟨atom, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨label, supported, same⟩ := List.mem_map.mp
      ((SourceCurrentNativeNormalizationInputs.actual_free expression inputs firstNames before after context first firstActual _).mp named)
    cases label with
    | inl fixed => exact firstFresh atom selected (same ▸ supported)
    | inr varied => exact inactive varied supported
  have secondAbsent : ∀ name ∈ atoms.map secondNames, name ∉ second.free := by
    intro name member named
    obtain ⟨atom, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨label, supported, same⟩ := List.mem_map.mp
      ((SourceCurrentNativeNormalizationInputs.actual_free expression inputs secondNames later final laterContext second secondActual _).mp named)
    cases label with
    | inl fixed => exact secondFresh atom selected (same ▸ supported)
    | inr varied => exact inactive varied supported
  rw [strip_absent _ _ after firstContext.normal firstAvailable firstAbsent,
    strip_absent _ _ final secondContext.normal secondAvailable secondAbsent, equal]

end MicroCFTA.SourceCurrentNativeNormalizedComparisonInactive
