import MicroCFTA.InternedPendingOrdinaryMismatch

/-!
# Live ordinary inputs at a pending source encounter

A pending request must differ from its earlier completed source site on a
live lexical input. An old probe cannot contain a fresh interned name.
The difference therefore selects an actual ordinary crossing. Its later
name occurs in the active ancestor's original Depth probe.
-/
namespace MicroCFTA.InternedPendingLiveMismatch
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback InternedStoredMuOrigins
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedLiveInputContext InternedLiveInputSupport InternedLiveInputReadiness
open InternedRequestAgreement InternedFreshProbeKeys InternedPendingOrdinaryMismatch
open InternedBinderProtocol (Reference NodeKey)

/-- Paired lexical inputs retain the actual route and the active fresh local. -/
def routeAtoms [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard)) : List (Reference × Reference) :=
  (earlier.zip current).map (fun pair => (pair.1.name, pair.2.name)) ++
    (.depth, .interned origin.entry.identity) :: origin.names.map (fun name => (name, name))

/-- The two maps recover the exact literal input lists of the two routes. -/
theorem routeAtoms_names [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard)) (lengths : earlier.length = current.length) :
    (routeAtoms origin earlier current).map Prod.fst = earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names ∧
    (routeAtoms origin earlier current).map Prod.snd = current.map Crossing.name ++ origin.localNames := by
  have first := congrArg (List.map InternedProbeChoiceSites.Crossing.name) (List.map_fst_zip (Nat.le_of_eq lengths))
  have second := congrArg (List.map Crossing.name) (List.map_snd_zip (Nat.le_of_eq lengths.symm))
  constructor
  · simpa [routeAtoms, List.map_map, Function.comp_def] using
      congrArg (fun names => names ++ .depth :: origin.names) first
  · simpa [routeAtoms, Origin.localNames, List.map_map, Function.comp_def] using
      congrArg (fun names => names ++ .interned origin.entry.identity :: origin.names) second

/-- A changed paired input is ordinary or fresh on the current route. -/
theorem routeAtoms_changed [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard))
    (current : List (Crossing Symbol Guard))
    (descriptors : earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
      current.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)))
    (fresh : ∀ crossing ∈ current, ∀ identity, crossing.name = .interned identity → origin.cut.nodes.next ≤ identity)
    (index : Nat) (atom : Reference × Reference) (member : (routeAtoms origin earlier current)[index]? = some atom)
    (different : atom.1 ≠ atom.2) :
    (∃ identity, origin.cut.nodes.next ≤ identity ∧ atom.2 = .interned identity) ∨
    ∃ (previous : InternedProbeChoiceSites.Crossing Symbol Guard) (actual : Crossing Symbol Guard) (level : Nat),
      earlier[index]? = some previous ∧ current[index]? = some actual ∧
      previous.body = actual.body ∧ previous.ordinary = true ∧ actual.name = .uninterned level ∧
      previous.depth.depth ≠ level ∧ atom = (.uninterned previous.depth.depth, .uninterned level) := by
  by_cases front : index < (earlier.zip current).length
  · rw [routeAtoms, List.getElem?_append_left (by simpa using front), List.getElem?_map] at member
    obtain ⟨pair, atPair, same⟩ := Option.map_eq_some_iff.mp member
    have paired := List.mem_of_getElem? atPair
    have positions := List.getElem?_zip_eq_some.mp atPair
    have selected := congrArg (fun list => list[index]?) descriptors
    simp only [List.getElem?_map, positions.1, positions.2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
    rcases Crossing.name_cases pair.2 with named | ⟨level, named⟩ | ⟨identity, named⟩
    · have flag : pair.1.ordinary = false := by simpa only [Crossing.probeChoice, named] using selected.2
      have equal : atom.1 = atom.2 := by rw [← same]; simp [InternedProbeChoiceSites.Crossing.name, flag, named]
      exact False.elim (different equal)
    · have flag : pair.1.ordinary = true := by simpa only [Crossing.probeChoice, named] using selected.2
      have atomSame : atom = (.uninterned pair.1.depth.depth, .uninterned level) := by
        rw [← same]; simp [InternedProbeChoiceSites.Crossing.name, flag, named]
      refine Or.inr ⟨pair.1, pair.2, level, positions.1, positions.2, selected.1, flag, named, ?_, atomSame⟩
      intro equal
      apply different
      simp [atomSame, equal]
    · exact Or.inl ⟨identity, fresh pair.2 (List.of_mem_zip paired).2 identity named, by rw [← same]; exact named⟩
  · rw [routeAtoms, List.getElem?_append_right (by simpa using Nat.le_of_not_gt front)] at member
    rcases List.mem_cons.mp (List.mem_of_getElem? member) with same | tail
    · exact Or.inl ⟨origin.entry.identity,
        Nat.le_of_eq (intern_miss_identity origin.cut.nodes key origin.missing).symm, by rw [same]⟩
    · obtain ⟨name, _, same⟩ := List.mem_map.mp tail
      exact False.elim (different (by rw [← same]))

/-- Live mismatch extraction preserves any fact about the selected active origin. -/
theorem encounter_live_mismatch_of [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard)
    (condition : Origin Symbol Guard key → Prop)
    (encounter : ∃ origin : Origin Symbol Guard key, ∃ smart body names before depth afterDepth ordinary crossings,
      condition origin ∧ Context before names ∧ Path origin.body origin.localNames (.binder smart body) names crossings ∧
      Grows origin.allocated before ∧
      (∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start before) ∧
      callback body (names.map Value.reference) .depth before = .done depth afterDepth ∧
      callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary final ∧
      Available final depth ∧ Available final ordinary ∧ key = muKey depth ordinary ∧ IsPending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ smart body names,
      ∃ current : List (Crossing Symbol Guard), ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard),
        condition origin ∧ Path origin.body origin.localNames (.binder smart body) names current ∧
        earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
          current.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
        (∀ crossing ∈ current, Grows origin.allocated crossing.before ∧ Grows crossing.start final) ∧
        (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) ∧
        ∃ (index : Nat) (previous : InternedProbeChoiceSites.Crossing Symbol Guard) (actual : Crossing Symbol Guard) (level : Nat),
          earlier[index]? = some previous ∧ current[index]? = some actual ∧
          previous.body = actual.body ∧ previous.ordinary = true ∧ actual.name = .uninterned level ∧
          previous.depth.depth ≠ level ∧
          ((.uninterned previous.depth.depth, .uninterned level), index) ∈
            liveInputs (.binder smart body) (routeAtoms origin earlier current).zipIdx ∧
          .uninterned level ∈ origin.depth.free := by
  classical
  obtain ⟨origin, smart, body, names, before, depth, afterDepth, ordinary, current,
    conditionHolds, context, path, initial, currentTraces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable, sameKey, pending⟩ := encounter
  have depthContext : Context afterDepth names := by
    simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
  have finalContext : Context final names := by
    simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
  have depthGrowth : Grows before afterDepth := by
    simpa only [depthDone, Outcome.state] using
      (callback_growing body (names.map Value.reference) .depth before context.normal.facts.coherent.valid).2
  have ordinaryGrowth : Grows afterDepth final := by
    simpa only [ordinaryDone, Outcome.state] using
      (callback_growing body (names.map Value.reference) (.uninterned depth.depth) afterDepth depthContext.normal.facts.coherent.valid).2
  have later := grows_trans depthGrowth ordinaryGrowth
  have cutAllocated : Grows origin.cut origin.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have cutGrowth : Grows origin.cut final := grows_trans cutAllocated (grows_trans initial later)
  have depthReference : depth.referenceOf = origin.depth.referenceOf := by
    have keys := sameKey.symm.trans origin.sameKey
    exact (InternedBinderProtocol.MuKey.mk.inj (NodeKey.mu.inj keys)).1
  have depthSame := resident_reference_injective final finalContext.normal.facts.coherent depth origin.depth
    depthAvailable.resident (resident_grows origin.cut final cutGrowth origin.depth origin.depthAvailable.resident) depthReference
  obtain ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, _, suffix, earlierTraces⟩ :=
    Origin.completed_representative origin path
  have lengths : earlier.length = current.length := by
    simpa only [List.length_map] using congrArg List.length descriptors
  have atomNames := routeAtoms_names origin earlier current lengths
  have previousNames : (routeAtoms origin earlier current).zipIdx.map (fun atom => atom.1.1) =
      earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names := by
    have erased := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 (routeAtoms origin earlier current))
    simpa only [List.map_map, Function.comp_def] using erased.trans atomNames.1
  have actualNames : (routeAtoms origin earlier current).zipIdx.map (fun atom => atom.1.2) = names := by
    have erased := congrArg (List.map Prod.snd) (List.zipIdx_map_fst 0 (routeAtoms origin earlier current))
    simpa only [List.map_map, Function.comp_def] using erased.trans (atomNames.2.trans (Path.names path).symm)
  have differs : ∃ atom ∈ liveInputs (.binder smart body) (routeAtoms origin earlier current).zipIdx, atom.1.1 ≠ atom.1.2 := by
    apply Classical.byContradiction
    intro none
    have agree : ∀ atom ∈ liveInputs (.binder smart body) (routeAtoms origin earlier current).zipIdx, atom.1.1 = atom.1.2 := by
      intro atom member
      apply Classical.byContradiction
      intro different
      exact none ⟨atom, member, different⟩
    have ready := not_pending_after_probes smart body (routeAtoms origin earlier current).zipIdx (fun atom => atom.1.1) (fun atom => atom.1.2) agree
      start before finish afterDepth final (by simpa only [previousNames] using previousContext)
      (by simpa only [actualNames] using context) previous depth ordinary
      (by simpa only [previousNames] using previousDone) (by simpa only [actualNames] using depthDone)
      (by simpa only [actualNames] using ordinaryDone) (grows_trans suffix cutGrowth)
    exact ready (sameKey ▸ pending)
  obtain ⟨atom, live, different⟩ := differs
  have fresh : ∀ crossing ∈ current, ∀ identity, crossing.name = .interned identity → origin.cut.nodes.next ≤ identity :=
    fun crossing member identity same => Crossing.interned_after origin crossing (currentTraces crossing member).1 identity same
  have supported : ∀ name, name ≠ .depth → atom.1.2 = name → name ∈ origin.depth.free := by
    intro name notDepth selected
    rw [← depthSame]
    exact (callback_other smart body (routeAtoms origin earlier current).zipIdx (fun atom => atom.1.2) .depth before afterDepth
      (by simpa only [actualNames] using context) (depth_available before) depth
      (by simpa only [actualNames] using depthDone) name notDepth).mpr (List.mem_map.mpr ⟨atom, live, selected⟩)
  rcases routeAtoms_changed origin earlier current descriptors fresh atom.2 atom.1
      (List.mem_zipIdx_iff_getElem?.mp (liveInputs_member _ _ _ live)) different with
    ⟨identity, recent, named⟩ | ⟨old, actual, level, oldAt, actualAt, bodies, flag, named, unequal, atomSame⟩
  · have present := supported (.interned identity) (by intro impossible; cases impossible) named
    have earlier := issued_free_below origin.cut.nodes origin.cutContext.normal.facts.coherent.valid.2
      origin.depth origin.depthAvailable.issued identity present
    omega
  · exact ⟨origin, smart, body, names, current, earlier, conditionHolds, path, descriptors,
      fun crossing member => ⟨(currentTraces crossing member).1, grows_trans (currentTraces crossing member).2 later⟩,
      earlierTraces, atom.2, old, actual, level, oldAt, actualAt, bodies, flag, named, unequal,
      (Prod.ext atomSame rfl : atom = ((.uninterned old.depth.depth, .uninterned level), atom.2)) ▸ live,
      supported (.uninterned level) (by intro impossible; cases impossible) (by rw [atomSame])⟩

/-- A pending encounter supplies a live ordinary mismatch retained by the active ancestor's original Depth probe. -/
theorem encounter_live_mismatch [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard)
    (encounter : InternedPendingSourceOrigins.Encounter key final) :
    ∃ origin : Origin Symbol Guard key, ∃ smart body names,
      ∃ current : List (Crossing Symbol Guard), ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard),
        Path origin.body origin.localNames (.binder smart body) names current ∧
        earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
          current.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
        (∀ crossing ∈ current, Grows origin.allocated crossing.before ∧ Grows crossing.start final) ∧
        (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) ∧
        ∃ (index : Nat) (previous : InternedProbeChoiceSites.Crossing Symbol Guard) (actual : Crossing Symbol Guard) (level : Nat),
          earlier[index]? = some previous ∧ current[index]? = some actual ∧
          previous.body = actual.body ∧ previous.ordinary = true ∧ actual.name = .uninterned level ∧
          previous.depth.depth ≠ level ∧
          ((.uninterned previous.depth.depth, .uninterned level), index) ∈
            liveInputs (.binder smart body) (routeAtoms origin earlier current).zipIdx ∧
          .uninterned level ∈ origin.depth.free := by
  obtain ⟨origin, smart, body, names, before, depth, afterDepth, ordinary, current, rest⟩ := encounter
  obtain ⟨origin, smart, body, names, current, earlier, _, result⟩ :=
    encounter_live_mismatch_of key final (fun _ => True)
      ⟨origin, smart, body, names, before, depth, afterDepth, ordinary, current, True.intro, rest⟩
  exact ⟨origin, smart, body, names, current, earlier, result⟩

/-- Closed execution derives the live mismatch and its actual old-probe support without admission premises. -/
theorem closed_live_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ smart body names,
      ∃ current : List (Crossing Symbol Guard), ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard),
        Path origin.body origin.localNames (.binder smart body) names current ∧
        earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
          current.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
        (∀ crossing ∈ current, Grows origin.allocated crossing.before ∧ Grows crossing.start final) ∧
        (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) ∧
        ∃ (index : Nat) (previous : InternedProbeChoiceSites.Crossing Symbol Guard) (actual : Crossing Symbol Guard) (level : Nat),
          earlier[index]? = some previous ∧ current[index]? = some actual ∧
          previous.body = actual.body ∧ previous.ordinary = true ∧ actual.name = .uninterned level ∧
          previous.depth.depth ≠ level ∧
          ((.uninterned previous.depth.depth, .uninterned level), index) ∈
            liveInputs (.binder smart body) (routeAtoms origin earlier current).zipIdx ∧
          .uninterned level ∈ origin.depth.free :=
  encounter_live_mismatch key final (InternedPendingSourceOrigins.closed_encounter expression key final pending)

/-- An ordinary name in the original Depth probe is a live capture of the active ancestor. -/
theorem origin_live_capture [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (level : Nat) (present : .uninterned level ∈ origin.depth.free) :
    .uninterned level ∈ liveInputs (.binder origin.smart origin.body) origin.names := by
  have observed := callback_other origin.smart origin.body origin.names id .depth origin.before origin.afterDepth
    (by simpa using origin.context) (depth_available origin.before) origin.depth
    (by simpa using origin.depthDone) (.uninterned level) (by intro impossible; cases impossible)
  simpa using observed.mp present

/-- An ordinary name in the original Depth probe occurs in the other key component unless it equals that probe's local. -/
theorem origin_ordinary_capture [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (level : Nat) (present : .uninterned level ∈ origin.depth.free) (different : level ≠ origin.depth.depth) :
    .uninterned level ∈ origin.ordinary.free := by
  have depthContext : Context origin.afterDepth origin.names := by
    simpa only [origin.depthDone, Outcome.state] using origin.context.callback origin.body .depth (depth_available origin.before)
  have observed := callback_other origin.smart origin.body origin.names id (.uninterned origin.depth.depth)
    origin.afterDepth origin.cut (by simpa using depthContext) (ordinary_available origin.afterDepth origin.depth.depth)
    origin.ordinary (by simpa using origin.ordinaryDone) (.uninterned level)
    (fun equal => different (Reference.uninterned.inj equal))
  apply observed.mpr
  simpa using origin_live_capture origin level present

/-- The live mismatch retains two actual Depth calls and compares the later level with both original key components. -/
theorem closed_live_depth_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ body firstNames secondNames firstStart secondStart firstDepth secondDepth firstEnd secondEnd,
      Context firstStart firstNames ∧ Context secondStart secondNames ∧
      callback body (firstNames.map Value.reference) .depth firstStart = .done firstDepth firstEnd ∧
      callback body (secondNames.map Value.reference) .depth secondStart = .done secondDepth secondEnd ∧
      firstDepth.depth ≠ secondDepth.depth ∧
      .uninterned secondDepth.depth ∈ origin.depth.free ∧
      .uninterned secondDepth.depth ∈ liveInputs (.binder origin.smart origin.body) origin.names ∧
      .uninterned secondDepth.depth ∈ origin.names ∧
      (secondDepth.depth ≠ origin.depth.depth → .uninterned secondDepth.depth ∈ origin.ordinary.free) ∧
      Grows firstEnd origin.cut ∧ Grows origin.allocated secondStart ∧ Grows secondEnd final := by
  obtain ⟨origin, smart, body, names, current, earlier, path, descriptors, currentTraces, earlierTraces,
    index, previous, actual, level, previousAt, actualAt, bodies, ordinary, named, different, live, present⟩ :=
    closed_live_mismatch expression key final pending
  obtain ⟨depth, depthDone, levelSame⟩ := ordinary_readback actual level named
  have originalLive := origin_live_capture origin level present
  have originalMember := liveInputs_member _ _ _ originalLive
  refine ⟨origin, actual.body, previous.names, actual.names, previous.before, actual.before, previous.depth, depth,
    previous.afterDepth, actual.start, previous.context, actual.context, ?_, depthDone,
    fun equal => different (equal.trans levelSame), ?_, ?_, ?_, ?_,
    (earlierTraces previous (List.mem_of_getElem? previousAt)).2,
    (currentTraces actual (List.mem_of_getElem? actualAt)).1,
    (currentTraces actual (List.mem_of_getElem? actualAt)).2⟩
  · simpa only [bodies] using previous.depthDone
  · simpa only [levelSame] using present
  · simpa only [levelSame] using originalLive
  · simpa only [levelSame] using originalMember
  · simpa only [levelSame] using origin_ordinary_capture origin level present

end MicroCFTA.InternedPendingLiveMismatch
