import MicroCFTA.InternedFreshOrdinaryActiveReplay

/-!
# Actual earlier repaired request pairs at pending source sites

Every earlier completed binder leaves a payload at its actual pair key.
That key differs from the active ancestor's missing key. The source route
retains both earlier callbacks and the actual completed request.
-/
namespace MicroCFTA.InternedFreshOrdinaryEarlierPair
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request)
open InternedNestedSpecialization
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryActiveOrigins
open InternedFreshOrdinaryActiveSite InternedFreshOrdinaryActiveReplay
open InternedBinderProtocol (Reference NodeKey)

/-- Every completed canonical request leaves a payload at its actual pair key for any callback. -/
theorem request_record [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (before : State Symbol Guard) (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : request smart depth ordinary callback before = .done value after) :
    ∃ record, after.nodeRecords (muKey depth ordinary) = some record := by
  cases found : before.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : before.nodeRecords (muKey depth ordinary) with
      | none => simp [request, found, stored] at done
      | some record =>
          simp only [request, found, stored, Outcome.done.injEq] at done
          obtain ⟨rfl, rfl⟩ := done
          exact ⟨record, stored⟩
  | none =>
      simp only [request, found] at done
      obtain ⟨body, afterBody, bodyDone, returned⟩ := bind_done _ _ _ _ done
      have same := (Outcome.done.inj returned).2
      rw [← same]
      exact keepFirst_present afterBody.nodeRecords (muKey depth ordinary)
        (.mu (Cache.intern before.nodes (muKey depth ordinary)).1 body depth ordinary)

/-- An earlier completed repaired binder has a complete pair different from the later active missing key. -/
theorem earlier_pair [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (smart : Bool) (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build (.binder smart body) environment before = .done value after)
    (growth : Grows after origin.cut) :
    ∃ depth afterDepth ordinary afterOrdinary record,
      callback body environment .depth before = .done depth afterDepth ∧
      callback body environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary afterOrdinary ∧
      request smart depth ordinary (callback body environment) afterOrdinary = .done value after ∧
      origin.cut.nodeRecords (muKey depth ordinary) = some record ∧
      (depth.referenceOf ≠ origin.depth.referenceOf ∨ ordinary.referenceOf ≠ origin.ordinary.referenceOf) := by
  rw [build] at done
  change ((callback body environment .depth before).bind fun depth middle =>
    (callback body environment (.uninterned (ordinaryLevel depth)) middle).bind fun ordinary cut =>
      request smart depth ordinary (callback body environment) cut) = .done value after at done
  obtain ⟨depth, afterDepth, depthDone, later⟩ := bind_done _ _ _ _ done
  obtain ⟨ordinary, afterOrdinary, ordinaryDone, requested⟩ := bind_done _ _ _ _ later
  obtain ⟨record, stored⟩ := request_record smart depth ordinary (callback body environment) afterOrdinary value after requested
  have retained := growth.nodeRecords _ _ stored
  refine ⟨depth, afterDepth, ordinary, afterOrdinary, record, depthDone, ordinaryDone, requested, retained, ?_⟩
  by_cases depthSame : depth.referenceOf = origin.depth.referenceOf
  · apply Or.inr
    intro ordinarySame
    have same : muKey depth ordinary = key := by rw [origin.sameKey]; simp only [muKey, depthSame, ordinarySame]
    rw [same, InternedNestedMissReadback.missing_record origin.cut origin.cutContext.normal.facts.coherent key origin.missing] at retained
    cases retained
  · exact Or.inl depthSame

/-- An actual pending site derives an earlier completed source route and both different earlier request probes. -/
theorem Site.scoped_earlier_pair [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) :
    ∃ earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard), ∃ start previous finish,
      earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
        site.crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
      build (.binder site.smart site.body)
        (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
        start = .done previous finish ∧
      Context start (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment) ∧
      Grows origin.before start ∧ Grows finish origin.cut ∧
      InternedFreshOrdinaryProbeChoiceSites.Captures (.reference .depth :: origin.environment) earlier ∧
      (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) ∧
      ∃ depth afterDepth ordinary afterOrdinary record,
        callback site.body
          (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
          .depth start = .done depth afterDepth ∧
        callback site.body
          (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
          (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary afterOrdinary ∧
        request site.smart depth ordinary
          (callback site.body (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment))
          afterOrdinary = .done previous finish ∧
        origin.cut.nodeRecords (muKey depth ordinary) = some record ∧
        (depth.referenceOf ≠ origin.depth.referenceOf ∨ ordinary.referenceOf ≠ origin.ordinary.referenceOf) := by
  obtain ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, initial, suffix, captures, traces⟩ :=
    Origin.completed_scoped_representative origin site.path
  exact ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, initial, suffix, captures, traces,
    InternedFreshOrdinaryEarlierPair.earlier_pair origin site.smart site.body _ start previous finish previousDone suffix⟩

/-- An actual pending site derives an earlier completed source route and both different earlier request probes. -/
theorem Site.earlier_pair [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) :
    ∃ earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard), ∃ start previous finish,
      earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
        site.crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
      build (.binder site.smart site.body)
        (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
        start = .done previous finish ∧
      Context start (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment) ∧
      Grows origin.before start ∧ Grows finish origin.cut ∧
      (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) ∧
      ∃ depth afterDepth ordinary afterOrdinary record,
        callback site.body
          (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
          .depth start = .done depth afterDepth ∧
        callback site.body
          (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
          (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary afterOrdinary ∧
        request site.smart depth ordinary
          (callback site.body (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment))
          afterOrdinary = .done previous finish ∧
        origin.cut.nodeRecords (muKey depth ordinary) = some record ∧
        (depth.referenceOf ≠ origin.depth.referenceOf ∨ ordinary.referenceOf ≠ origin.ordinary.referenceOf) := by
  obtain ⟨earlier, start, previous, finish, descriptors, completed, context, initial, suffix, _, traces, pair⟩ :=
    Site.scoped_earlier_pair site
  exact ⟨earlier, start, previous, finish, descriptors, completed, context, initial, suffix, traces, pair⟩

end MicroCFTA.InternedFreshOrdinaryEarlierPair
