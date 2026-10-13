import MicroCFTA.InternedProfilePendingEncounter
import MicroCFTA.InternedSpecialKeyCompletion
import MicroCFTA.InternedProbeOpacity

/-!
# The remaining profile cases of a closed pending source execution

The two smart-empty keys are excluded for unrestricted syntax. Every
remaining actual encountered callback is either opaque, or it has a
nonempty fixed captured-reference profile. Both actual probes have the
same opacity. This theorem does not assert that either remaining case
can occur.
-/
namespace MicroCFTA.InternedPendingProfileBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedNestedProvenance InternedProbeProvenance InternedProfileTraceSites InternedSpecialKeyReadiness
open InternedSpecialProbeKeys InternedSpecialKeyCompletion
open InternedRootProfile InternedProfileCallbackForm
open InternedBinderProtocol (Reference NodeKey)

/-- An arbitrary closed pending run has an actual verified callback in one of the two remaining profile classes. -/
theorem closed_remaining [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (selected : NodeKey) (final : State Symbol Guard)
    (stopped : build expression [] empty = .pending selected final) :
    ∃ body, ∃ names : List Reference, ∃ before depth afterDepth ordinary,
      Context before (names.map Value.reference) ∧
      callback body (names.map Value.reference) .depth before = .done depth afterDepth ∧
      callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary final ∧
      selected = muKey depth ordinary ∧ IsPending selected final ∧
      ((symbolic body ((names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map profile) = none ∧
          profile depth = none ∧ profile ordinary = none) ∨
        ∃ captured, symbolic body ((names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map profile) = some captured ∧
          captures captured ≠ [] ∧ profile depth ≠ none ∧ profile ordinary ≠ none) := by
  obtain ⟨body, names, before, depth, afterDepth, ordinary, context, depthDone, ordinaryDone, sameKey, pending⟩ :=
    InternedProfilePendingEncounter.closed_encounter expression selected final stopped
  refine ⟨body, names, before, depth, afterDepth, ordinary, context, depthDone, ordinaryDone, sameKey, pending, ?_⟩
  have depthHidden := InternedProbeOpacity.callback_opaque body (names.map Value.reference) .depth before
    context.normal context.depth.inputs context.heap depth afterDepth depthDone
  have afterContext : Context afterDepth (names.map Value.reference) := by
    simpa only [depthDone, Outcome.state] using InternedSpecialKeyReadiness.Context.callback context body .depth (depth_available before)
  have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: names.map Value.reference) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ordinary_available afterDepth depth.depth
    · exact afterContext.inputs value member
  have ordinaryHidden := InternedProbeOpacity.callback_opaque body (names.map Value.reference) (.uninterned depth.depth) afterDepth
    afterContext.normal ordinaryInputs afterContext.heap ordinary final ordinaryDone
  cases computed : symbolic body ((names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map profile) with
  | none => exact Or.inl ⟨rfl, depthHidden.mpr computed, ordinaryHidden.mpr computed⟩
  | some captured =>
      refine Or.inr ⟨captured, rfl, ?_, ?_, ?_⟩
      · intro emptyCaptures
        have classified : Classified body ((names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map profile) (usesArgument captured) :=
          ⟨captured, computed, emptyCaptures, rfl⟩
        have special := (source_classified body (names.map Value.reference) before afterDepth final context depth ordinary depthDone ordinaryDone _).mpr classified
        exact closed_safe expression (usesArgument captured) final (by simpa only [sameKey, special] using stopped)
      · intro hidden
        rw [computed] at depthHidden
        have impossible := depthHidden.mp hidden
        cases impossible
      · intro hidden
        rw [computed] at ordinaryHidden
        have impossible := ordinaryHidden.mp hidden
        cases impossible

end MicroCFTA.InternedPendingProfileBoundary
