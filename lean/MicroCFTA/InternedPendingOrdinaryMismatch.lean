import MicroCFTA.InternedActiveSourceReplay

/-!
# A pending source encounter requires different ordinary probe levels

The active ancestor already executed a matching probe route. Fresh locals
on the later route cannot affect an old encountered probe. If corresponding
ordinary levels also match, the earlier complete request excludes pending
readback. Thus a hypothetical pending closed run supplies an actual level
mismatch between corresponding ordinary entries.
-/
namespace MicroCFTA.InternedPendingOrdinaryMismatch
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback InternedStoredMuOrigins
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedLiveSiteReadiness InternedOccurrenceObservations InternedRequestAgreement InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeKey)

/-- Corresponding ordinary entries use different actual Unint levels. -/
def DifferentOrdinary [DecidableEq (EdgeKey Symbol Guard)]
    (earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard)) (current : List (Crossing Symbol Guard)) : Prop :=
  ∃ (index : Nat) (previous : InternedProbeChoiceSites.Crossing Symbol Guard) (actual : Crossing Symbol Guard) (level : Nat),
    earlier[index]? = some previous ∧ current[index]? = some actual ∧
    previous.ordinary = true ∧ actual.name = .uninterned level ∧ previous.depth.depth ≠ level

/-- Unchanged lexical tails satisfy the fresh-change comparison. -/
theorem freshChanges_refl (cutoff : Nat) (names : List Reference) : FreshChanges cutoff names names := by
  induction names with
  | nil => exact .nil
  | cons name rest ih => exact .cons (Or.inl rfl) ih

/-- Independent lexical prefixes and tails preserve their position-wise comparison. -/
theorem freshChanges_append (left : FreshChanges cutoff first second) (right : FreshChanges cutoff rest tail) :
    FreshChanges cutoff (first ++ rest) (second ++ tail) := by
  induction left with
  | nil => exact right
  | cons related paired ih => exact .cons related ih

/-- Matching ordinary levels leave only the already bounded fresh-name differences. -/
theorem freshChanges_of_no_mismatch [DecidableEq (EdgeKey Symbol Guard)] (cutoff : Nat)
    (earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard)) (current : List (Crossing Symbol Guard))
    (flags : earlier.map InternedProbeChoiceSites.Crossing.ordinary = current.map Crossing.probeChoice)
    (fresh : ∀ crossing ∈ current, ∀ identity, crossing.name = .interned identity → cutoff ≤ identity)
    (none : ¬ DifferentOrdinary earlier current) :
    FreshChanges cutoff (earlier.map InternedProbeChoiceSites.Crossing.name) (current.map Crossing.name) := by
  induction earlier generalizing current with
  | nil =>
      cases current with
      | nil => exact .nil
      | cons head tail => simp at flags
  | cons previous rest ih =>
      cases current with
      | nil => simp at flags
      | cons actual tail =>
          have flagsPair := List.cons.inj flags
          have tailNone : ¬ DifferentOrdinary rest tail := by
            rintro ⟨index, a, b, level, aAt, bAt, ordinary, named, different⟩
            exact none ⟨index + 1, a, b, level, by simpa using aAt, by simpa using bAt, ordinary, named, different⟩
          refine .cons ?_ (ih tail flagsPair.2 (fun crossing member => fresh crossing (List.mem_cons_of_mem actual member)) tailNone)
          rcases Crossing.name_cases actual with named | ⟨level, named⟩ | ⟨identity, named⟩
          · have flag : previous.ordinary = false := by
              simpa only [Crossing.probeChoice, named] using flagsPair.1
            exact Or.inl (by simp [InternedProbeChoiceSites.Crossing.name, flag, named])
          · have flag : previous.ordinary = true := by
              simpa only [Crossing.probeChoice, named] using flagsPair.1
            have same : previous.depth.depth = level := by
              by_cases equal : previous.depth.depth = level
              · exact equal
              · exact False.elim (none ⟨0, previous, actual, level, rfl, rfl, flag, named, equal⟩)
            exact Or.inl (by simp [InternedProbeChoiceSites.Crossing.name, flag, named, same])
          · exact Or.inr ⟨identity, fresh actual List.mem_cons_self identity named, named⟩

/-- Every hypothetical pending encounter has an actual mismatched ordinary level on its two corresponding routes. -/
theorem encounter_mismatch [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard)
    (encounter : InternedPendingSourceOrigins.Encounter key final) :
    ∃ origin : Origin Symbol Guard key, ∃ smart body names,
      ∃ current : List (Crossing Symbol Guard), ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard),
        Path origin.body origin.localNames (.binder smart body) names current ∧
        earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
          current.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
        DifferentOrdinary earlier current ∧
        (∀ crossing ∈ current, Grows origin.allocated crossing.before ∧ Grows crossing.start final) ∧
        (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) := by
  classical
  obtain ⟨origin, smart, body, names, before, depth, afterDepth, ordinary, current,
    context, path, initial, currentTraces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable, sameKey, pending⟩ := encounter
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
  have depthOld : Available origin.cut depth := depthSame ▸ origin.depthAvailable
  obtain ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, _, suffix, earlierTraces⟩ :=
    Origin.completed_representative origin path
  have flags : earlier.map InternedProbeChoiceSites.Crossing.ordinary = current.map Crossing.probeChoice := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.snd) descriptors
  refine ⟨origin, smart, body, names, current, earlier, path, descriptors, ?_,
    fun crossing member => ⟨(currentTraces crossing member).1, grows_trans (currentTraces crossing member).2 later⟩, earlierTraces⟩
  by_cases different : DifferentOrdinary earlier current
  · exact different
  exfalso
  have fresh : ∀ crossing ∈ current, ∀ identity, crossing.name = .interned identity → origin.cut.nodes.next ≤ identity :=
    fun crossing member identity same => Crossing.interned_after origin crossing (currentTraces crossing member).1 identity same
  have prefixes := freshChanges_of_no_mismatch origin.cut.nodes.next earlier current flags fresh different
  have tails : FreshChanges origin.cut.nodes.next (.depth :: origin.names) origin.localNames := by
    apply Paired.cons _ (freshChanges_refl _ _)
    exact Or.inr ⟨origin.entry.identity, Nat.le_of_eq (InternedFreshProbeKeys.intern_miss_identity origin.cut.nodes key origin.missing).symm, rfl⟩
  have changed : FreshChanges origin.cut.nodes.next
      (earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names) names := by
    rw [Path.names path]
    exact freshChanges_append prefixes tails
  exact (names_not_pending smart body _ names origin.cut origin.cutContext.normal.facts.coherent.valid changed
    start before finish afterDepth final previousContext context previous depth ordinary previousDone depthDone ordinaryDone
    (grows_trans suffix cutGrowth) depthOld) (sameKey ▸ pending)

/-- Any closed source run that stops pending must contain the actual ordinary-level mismatch above. -/
theorem closed_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ smart body names,
      ∃ current : List (Crossing Symbol Guard), ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard),
        Path origin.body origin.localNames (.binder smart body) names current ∧
        earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
          current.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
        DifferentOrdinary earlier current ∧
        (∀ crossing ∈ current, Grows origin.allocated crossing.before ∧ Grows crossing.start final) ∧
        (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) :=
  encounter_mismatch key final (InternedPendingSourceOrigins.closed_encounter expression key final pending)

/-- An actual ordinary entry retains the completed Depth call that computed its name. -/
theorem ordinary_readback [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard)
    (level : Nat) (named : crossing.name = .uninterned level) :
    ∃ depth, callback crossing.body (crossing.names.map Value.reference) .depth crossing.before = .done depth crossing.start ∧
      depth.depth = level := by
  rcases crossing with ⟨smart, body, names, before, name, start, context, entered⟩
  cases entered with
  | depth => cases named
  | ordinary depth afterDepth done => exact ⟨depth, done, Reference.uninterned.inj named⟩
  | fresh => cases named

/-- A hypothetical pending closed run supplies two completed calls of the same source body with different cached depths. -/
theorem closed_depth_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ body firstNames secondNames firstStart secondStart firstDepth secondDepth firstEnd secondEnd,
      Context firstStart firstNames ∧ Context secondStart secondNames ∧
      callback body (firstNames.map Value.reference) .depth firstStart = .done firstDepth firstEnd ∧
      callback body (secondNames.map Value.reference) .depth secondStart = .done secondDepth secondEnd ∧
      firstDepth.depth ≠ secondDepth.depth ∧ Grows firstEnd origin.cut ∧
      Grows origin.allocated secondStart ∧ Grows secondEnd final := by
  obtain ⟨origin, smart, body, names, current, earlier, path, descriptors, different, currentTraces, earlierTraces⟩ :=
    closed_mismatch expression key final pending
  obtain ⟨index, previous, actual, level, previousAt, actualAt, ordinary, named, different⟩ := different
  have same : previous.body = actual.body := by
    have selected := congrArg (fun list => list[index]?) descriptors
    simp only [List.getElem?_map, previousAt, actualAt, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
    exact selected.1
  obtain ⟨depth, depthDone, levelSame⟩ := ordinary_readback actual level named
  have previousMember := List.mem_of_getElem? previousAt
  have actualMember := List.mem_of_getElem? actualAt
  refine ⟨origin, actual.body, previous.names, actual.names, previous.before, actual.before, previous.depth, depth,
    previous.afterDepth, actual.start, previous.context, actual.context, ?_, depthDone,
    fun equal => different (equal.trans levelSame), (earlierTraces previous previousMember).2,
    (currentTraces actual actualMember).1, (currentTraces actual actualMember).2⟩
  simpa only [same] using previous.depthDone

end MicroCFTA.InternedPendingOrdinaryMismatch
