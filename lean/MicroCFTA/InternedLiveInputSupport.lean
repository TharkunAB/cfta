import MicroCFTA.InternedLiveInputReadiness

/-!
# Old probes determine the live lexical inputs

The depth callback exposes each interned captured name. If its returned
record predates a cutoff, every changed input at or above that cutoff is
absent from the live support. This gives exact request readiness without
an assumed callback equation.
-/
namespace MicroCFTA.InternedLiveInputSupport
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins
open InternedFreeAbsenceContext InternedLiveInputContext InternedLiveInputReadiness
open InternedFreeNameSemantics InternedRootProfile
open InternedBinderProtocol (Reference)
variable {Atom : Type}

/-- Abstract live inputs commute with arbitrary literal-reference maps. -/
theorem liveInputs_map (expression : Syntax Symbol Guard) (atoms : List Atom) (names : Atom → Reference) :
    liveInputs expression (atoms.map names) = (liveInputs expression atoms).map names := by
  have mapped := evaluate_map names expression (atoms.map (fun atom => some [atom])) (atoms.map (fun atom => [atom]))
  simpa [liveInputs, List.map_map, Function.comp_def, InternedProfileSemantics.mapNames] using mapped

/-- Every live abstract input is one of the supplied lexical atoms. -/
theorem liveInputs_member (expression : Syntax Symbol Guard) (atoms : List Atom) (atom : Atom)
    (member : atom ∈ liveInputs expression atoms) : atom ∈ atoms := by
  obtain ⟨names, included, present⟩ := evaluate_origins expression
    (atoms.map (fun atom => some [atom])) (atoms.map (fun atom => [atom])) atom member
  obtain ⟨original, source, same⟩ := List.mem_map.mp included
  rw [← same] at present
  have equal := List.mem_singleton.mp present
  exact equal ▸ source

/-- A completed callback exposes each live external input other than its supplied name. -/
theorem callback_other [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (atoms : List Atom) (names : Atom → Reference) (argument : Reference)
    (state final : State Symbol Guard) (context : Context state (atoms.map names))
    (available : Available state (.reference argument)) (value : Value Symbol Guard)
    (completed : callback body ((atoms.map names).map Value.reference) argument state = .done value final)
    (name : Reference) (different : name ≠ argument) :
    name ∈ value.free ↔ name ∈ (liveInputs (.binder smart body) atoms).map names := by
  have observation := InternedSourceFreeNames.callback_other body _ argument state context.normal
    (context.local argument available).inputs context.freeNames context.profiles value final completed name different
  rw [← InternedFreeNameForm.binder_captures smart] at observation
  rw [← liveInputs_map]
  simpa only [liveInputs, List.map_map, Function.comp_def, profile, Value.free] using observation

/-- An old actual depth probe forces agreement on all live inputs when every changed input is fresh. -/
theorem agreement_of_old_probe [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (atoms : List Atom) (firstMap secondMap : Atom → Reference) (cut : State Symbol Guard) (valid : Valid cut)
    (changed : ∀ atom ∈ atoms, firstMap atom ≠ secondMap atom →
      ∃ identity, cut.nodes.next ≤ identity ∧ secondMap atom = .interned identity)
    (state final : State Symbol Guard) (context : Context state (atoms.map secondMap))
    (depth : Value Symbol Guard)
    (completed : callback body ((atoms.map secondMap).map Value.reference) .depth state = .done depth final)
    (old : Available cut depth) :
    ∀ atom ∈ liveInputs (.binder smart body) atoms, firstMap atom = secondMap atom := by
  intro atom member
  by_cases different : firstMap atom = secondMap atom
  · exact different
  exfalso
  obtain ⟨identity, fresh, same⟩ := changed atom (liveInputs_member _ atoms atom member) different
  have present : .interned identity ∈ depth.free :=
    (callback_other smart body atoms secondMap .depth state final context (depth_available state) depth completed
      (.interned identity) (by intro impossible; cases impossible)).mpr (List.mem_map.mpr ⟨atom, member, same⟩)
  have earlier := InternedFreshProbeKeys.issued_free_below cut.nodes valid.2 depth old.issued identity present
  omega

/-- An earlier completed site excludes pending readback when only fresh captured names differ. -/
theorem not_pending_of_fresh_changes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (atoms : List Atom) (firstMap secondMap : Atom → Reference) (cut : State Symbol Guard) (valid : Valid cut)
    (changed : ∀ atom ∈ atoms, firstMap atom ≠ secondMap atom →
      ∃ identity, cut.nodes.next ≤ identity ∧ secondMap atom = .interned identity)
    (left right afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left (atoms.map firstMap)) (rc : Context right (atoms.map secondMap))
    (first depth ordinary : Value Symbol Guard)
    (firstDone : build (.binder smart body) ((atoms.map firstMap).map Value.reference) left = .done first afterLeft)
    (depthDone : callback body ((atoms.map secondMap).map Value.reference) .depth right = .done depth afterRightDepth)
    (ordinaryDone : callback body ((atoms.map secondMap).map Value.reference) (.uninterned depth.depth) afterRightDepth = .done ordinary afterRight)
    (growth : Grows afterLeft afterRight) (old : Available cut depth) :
    ¬ IsPending (muKey depth ordinary) afterRight := by
  exact not_pending_after_probes smart body atoms firstMap secondMap
    (agreement_of_old_probe smart body atoms firstMap secondMap cut valid changed right afterRightDepth rc depth depthDone old)
    left right afterLeft afterRightDepth afterRight lc rc first depth ordinary firstDone depthDone ordinaryDone growth

end MicroCFTA.InternedLiveInputSupport
