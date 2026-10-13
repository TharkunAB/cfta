import MicroCFTA.InternedPendingJointKey

/-!
# Exact earlier and pending probe pairs

The earlier completed source site has a complete request record before
the active reservation. Its probe pair differs from the pending pair.
The later site returns both original probe records exactly. Live mismatch
extraction keeps these facts attached to the same source route.
-/
namespace MicroCFTA.InternedPendingJointKeyMismatch
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedLiveInputContext InternedLiveInputSupport InternedLiveInputReadiness
open InternedRequestAgreement InternedFreshProbeKeys InternedPendingLiveMismatch InternedPendingJointKey
open InternedBinderProtocol (Reference NodeKey)

/-- Every completed source request leaves a complete record at its actual pair key. -/
theorem request_record [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (coherent : Coherent before) (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : request smart depth ordinary (callback body environment) before = .done value after) :
    ∃ record, after.nodeRecords (muKey depth ordinary) = some record := by
  cases found : before.nodes.table (muKey depth ordinary) with
  | none =>
      obtain ⟨actual, afterBody, _, stored, _⟩ := request_miss_record smart body environment depth ordinary before coherent found value after done
      exact ⟨_, stored⟩
  | some entry =>
      cases stored : before.nodeRecords (muKey depth ordinary) with
      | none => simp [request, found, stored] at done
      | some record =>
          simp only [request, found, stored, Outcome.done.injEq] at done
          obtain ⟨rfl, rfl⟩ := done
          exact ⟨record, stored⟩

/-- An earlier completed binder exposes two actual probes whose complete pair differs from the active missing key. -/
theorem earlier_pair [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (smart : Bool) (body : Syntax Symbol Guard) (names : List Reference)
    (before : State Symbol Guard) (context : Context before names) (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build (.binder smart body) (names.map Value.reference) before = .done value after)
    (growth : Grows after origin.cut) :
    ∃ depth afterDepth ordinary afterOrdinary record,
      callback body (names.map Value.reference) .depth before = .done depth afterDepth ∧
      callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary afterOrdinary ∧
      request smart depth ordinary (callback body (names.map Value.reference)) afterOrdinary = .done value after ∧
      origin.cut.nodeRecords (muKey depth ordinary) = some record ∧
      (depth.referenceOf ≠ origin.depth.referenceOf ∨ ordinary.referenceOf ≠ origin.ordinary.referenceOf) := by
  rw [build] at done
  change ((callback body (names.map Value.reference) .depth before).bind fun depth middle =>
    (callback body (names.map Value.reference) (.uninterned depth.depth) middle).bind fun ordinary cut =>
      request smart depth ordinary (callback body (names.map Value.reference)) cut) = .done value after at done
  obtain ⟨depth, afterDepth, depthDone, later⟩ := bind_done _ _ _ _ done
  obtain ⟨ordinary, afterOrdinary, ordinaryDone, requested⟩ := bind_done _ _ _ _ later
  have depthContext : Context afterDepth names := by
    simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
  have requestContext : Context afterOrdinary names := by
    simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
  obtain ⟨record, stored⟩ := request_record smart body (names.map Value.reference) depth ordinary afterOrdinary
    requestContext.normal.facts.coherent value after requested
  have retained := growth.nodeRecords _ _ stored
  refine ⟨depth, afterDepth, ordinary, afterOrdinary, record, depthDone, ordinaryDone, requested, retained, ?_⟩
  by_cases depthDifferent : depth.referenceOf = origin.depth.referenceOf
  · apply Or.inr
    intro ordinarySame
    have same : muKey depth ordinary = key := by rw [origin.sameKey]; simp only [muKey, depthDifferent, ordinarySame]
    rw [same, missing_record origin.cut origin.cutContext.normal.facts.coherent key origin.missing] at retained
    cases retained
  · exact Or.inl depthDifferent

/-- One route retains the exact earlier pair, the live changed position, and the earlier producer of its later level. -/
def Mismatch [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Prop :=
  ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard), ∃ start previous finish,
    earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
      site.crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
    build (.binder site.smart site.body)
      ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names).map Value.reference) start = .done previous finish ∧
    Context start (earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names) ∧
    Grows finish origin.cut ∧
    (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) ∧
    ∃ oldDepth afterDepth oldOrdinary afterOrdinary record,
      callback site.body ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names).map Value.reference)
        .depth start = .done oldDepth afterDepth ∧
      callback site.body ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names).map Value.reference)
        (.uninterned oldDepth.depth) afterDepth = .done oldOrdinary afterOrdinary ∧
      request site.smart oldDepth oldOrdinary
        (callback site.body ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names).map Value.reference))
        afterOrdinary = .done previous finish ∧
      origin.cut.nodeRecords (muKey oldDepth oldOrdinary) = some record ∧
      (oldDepth.referenceOf ≠ origin.depth.referenceOf ∨ oldOrdinary.referenceOf ≠ origin.ordinary.referenceOf) ∧
      ∃ (index : Nat) (first : InternedProbeChoiceSites.Crossing Symbol Guard) (second : Crossing Symbol Guard) (level : Nat),
        earlier[index]? = some first ∧ site.crossings[index]? = some second ∧
        first.body = second.body ∧ first.ordinary = true ∧ second.name = .uninterned level ∧
        first.depth.depth ≠ level ∧
        ((.uninterned first.depth.depth, .uninterned level), index) ∈
          liveInputs (.binder site.smart site.body) (routeAtoms origin earlier site.crossings).zipIdx ∧
        .uninterned level ∈ origin.depth.free ∧
        .uninterned level ∈ liveInputs (.binder origin.smart origin.body) origin.names ∧
        ∃ outer captures outerStart outerDepth outerEnd,
          captures.length < origin.names.length ∧ Context outerStart captures ∧
          callback outer (captures.map Value.reference) .depth outerStart = .done outerDepth outerEnd ∧
          outerDepth.depth = level ∧ Grows outerEnd origin.before

/-- Joint-key extraction keeps the mismatch attached to the same exact current and earlier source calls. -/
theorem Site.mismatch [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Mismatch site := by
  classical
  obtain ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, _, suffix, earlierTraces⟩ :=
    Origin.completed_representative origin site.path
  obtain ⟨oldDepth, afterDepth, oldOrdinary, afterOrdinary, record, oldDepthDone, oldOrdinaryDone, oldRequestDone, oldStored, oldDifferent⟩ :=
    earlier_pair origin site.smart site.body _ start previousContext previous finish previousDone suffix
  have lengths : earlier.length = site.crossings.length := by
    simpa only [List.length_map] using congrArg List.length descriptors
  have atomNames := routeAtoms_names origin earlier site.crossings lengths
  have previousNames : (routeAtoms origin earlier site.crossings).zipIdx.map (fun atom => atom.1.1) =
      earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: origin.names := by
    have erased := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 (routeAtoms origin earlier site.crossings))
    simpa only [List.map_map, Function.comp_def] using erased.trans atomNames.1
  have actualNames : (routeAtoms origin earlier site.crossings).zipIdx.map (fun atom => atom.1.2) = site.names := by
    have erased := congrArg (List.map Prod.snd) (List.zipIdx_map_fst 0 (routeAtoms origin earlier site.crossings))
    simpa only [List.map_map, Function.comp_def] using erased.trans (atomNames.2.trans (Path.names site.path).symm)
  have differs : ∃ atom ∈ liveInputs (.binder site.smart site.body) (routeAtoms origin earlier site.crossings).zipIdx,
      atom.1.1 ≠ atom.1.2 := by
    apply Classical.byContradiction
    intro none
    have agree : ∀ atom ∈ liveInputs (.binder site.smart site.body) (routeAtoms origin earlier site.crossings).zipIdx,
        atom.1.1 = atom.1.2 := by
      intro atom member
      apply Classical.byContradiction
      intro different
      exact none ⟨atom, member, different⟩
    have ready := not_pending_after_probes site.smart site.body (routeAtoms origin earlier site.crossings).zipIdx
      (fun atom => atom.1.1) (fun atom => atom.1.2) agree start site.before finish site.afterDepth final
      (by simpa only [previousNames] using previousContext) (by simpa only [actualNames] using site.context)
      previous origin.depth origin.ordinary (by simpa only [previousNames] using previousDone)
      (by simpa only [actualNames] using site.depthDone) (by simpa only [actualNames] using site.ordinaryDone)
      (grows_trans suffix site.growth.2.2)
    exact ready (origin.sameKey ▸ site.pending)
  obtain ⟨atom, live, different⟩ := differs
  have fresh : ∀ crossing ∈ site.crossings, ∀ identity, crossing.name = .interned identity → origin.cut.nodes.next ≤ identity :=
    fun crossing member identity same => Crossing.interned_after origin crossing (site.traces crossing member).1 identity same
  have supported : ∀ name, name ≠ .depth → atom.1.2 = name → name ∈ origin.depth.free := by
    intro name notDepth selected
    exact (callback_other site.smart site.body (routeAtoms origin earlier site.crossings).zipIdx (fun atom => atom.1.2)
      .depth site.before site.afterDepth (by simpa only [actualNames] using site.context) (depth_available site.before) origin.depth
      (by simpa only [actualNames] using site.depthDone) name notDepth).mpr (List.mem_map.mpr ⟨atom, live, selected⟩)
  rcases routeAtoms_changed origin earlier site.crossings descriptors fresh atom.2 atom.1
      (List.mem_zipIdx_iff_getElem?.mp (liveInputs_member _ _ _ live)) different with
    ⟨identity, recent, named⟩ | ⟨first, second, level, firstAt, secondAt, bodies, flag, named, unequal, atomSame⟩
  · have present := supported (.interned identity) (by intro impossible; cases impossible) named
    have earlier := issued_free_below origin.cut.nodes origin.cutContext.normal.facts.coherent.valid.2
      origin.depth origin.depthAvailable.issued identity present
    omega
  · have present := supported (.uninterned level) (by intro impossible; cases impossible) (by rw [atomSame])
    have originalLive := origin_live_capture origin level present
    obtain ⟨outer, captures, outerStart, outerDepth, outerEnd, shorter, outerContext, outerDone, sameLevel, outerGrowth⟩ :=
      site.captures level (liveInputs_member _ _ _ originalLive)
    exact ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, suffix, earlierTraces,
      oldDepth, afterDepth, oldOrdinary, afterOrdinary, record, oldDepthDone, oldOrdinaryDone, oldRequestDone, oldStored, oldDifferent,
      atom.2, first, second, level, firstAt, secondAt, bodies, flag, named, unequal,
      (Prod.ext atomSame rfl : atom = ((.uninterned first.depth.depth, .uninterned level), atom.2)) ▸ live,
      present, originalLive, outer, captures, outerStart, outerDepth, outerEnd, shorter, outerContext, outerDone, sameLevel, outerGrowth⟩

/-- Every hypothetical closed pending run supplies the same-site joint-key mismatch and its shorter producer history. -/
theorem closed_joint_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final, Mismatch site := by
  obtain ⟨origin, ⟨site⟩⟩ := closed_site expression key final pending
  exact ⟨origin, site, Site.mismatch site⟩

end MicroCFTA.InternedPendingJointKeyMismatch
