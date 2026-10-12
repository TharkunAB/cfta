import MicroCFTA.InternedNestedPendingOrigin

/-!
# Any pending alias loses its ancestor's fresh name in both probes

The complete source trace supplies the actual earlier reservation. Its
fresh name was absent from both earlier available probes. Canonical
readback makes every resident pair with that key the same complete records.
Thus any hypothetical pending alias lies in the absent-name case.
-/
namespace MicroCFTA.InternedPendingOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedBinderProtocol (NodeKey)

/-- An actual pending origin supplies a genuinely new issued name absent from every resident representation of its key. -/
theorem Origin.probe_absence {key : NodeKey} {state : State Symbol Guard}
    (origin : Origin key state) (coherent : Coherent state) :
    ∃ before identity, Grows before state ∧ before.nodes.table key = none ∧
      before.nodes.issued identity = none ∧ state.nodes.issued identity = some key ∧
      ∀ depth ordinary, Resident state depth → Resident state ordinary → muKey depth ordinary = key →
        .interned identity ∉ depth.free ∧ .interned identity ∉ ordinary.free := by
  obtain ⟨before, oldDepth, oldOrdinary, keyEq, missing, earlierCoherent, depthAvailable, ordinaryAvailable, growth, installed⟩ := origin
  let entry := (Cache.intern before.nodes key).1
  have fresh : entry.identity = before.nodes.next := intern_miss_identity before.nodes key missing
  have unused : before.nodes.issued entry.identity = none := by
    cases prior : before.nodes.issued entry.identity with
    | none => rfl
    | some selected =>
        have bounded := earlierCoherent.valid.2.1 entry.identity selected prior
        rw [fresh] at bounded
        omega
  have issued : state.nodes.issued entry.identity = some key :=
    (coherent.valid.2.2 key entry installed).2
  have depthAbsent : .interned entry.identity ∉ oldDepth.free := by
    rw [fresh]
    exact next_absent before.nodes earlierCoherent.valid.2 oldDepth depthAvailable.issued
  have ordinaryAbsent : .interned entry.identity ∉ oldOrdinary.free := by
    rw [fresh]
    exact next_absent before.nodes earlierCoherent.valid.2 oldOrdinary ordinaryAvailable.issued
  have depthResident := resident_grows before state growth oldDepth depthAvailable.resident
  have ordinaryResident := resident_grows before state growth oldOrdinary ordinaryAvailable.resident
  refine ⟨before, entry.identity, growth, missing, unused, issued, ?_⟩
  intro depth ordinary newDepthResident newOrdinaryResident same
  have references : depth.referenceOf = oldDepth.referenceOf ∧ ordinary.referenceOf = oldOrdinary.referenceOf := by
    simpa only [muKey, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq] using same.trans keyEq
  have depthEq := resident_reference_injective state coherent depth oldDepth newDepthResident depthResident references.1
  have ordinaryEq := resident_reference_injective state coherent ordinary oldOrdinary newOrdinaryResident ordinaryResident references.2
  simpa only [depthEq, ordinaryEq] using And.intro depthAbsent ordinaryAbsent

/-- Full arbitrary closed source syntax can reach a pending key only when both resident probes omit the actual ancestor's fresh name. -/
theorem closed_pending_fresh_absent [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (state : State Symbol Guard) (pending : build expression [] empty = .pending key state) :
    ∃ before identity, Grows before state ∧ before.nodes.table key = none ∧
      before.nodes.issued identity = none ∧ state.nodes.issued identity = some key ∧
      ∀ depth ordinary, Resident state depth → Resident state ordinary → muKey depth ordinary = key →
        .interned identity ∉ depth.free ∧ .interned identity ∉ ordinary.free := by
  have facts : Facts state := by simpa only [pending, Outcome.state] using (closed_verified expression).facts
  exact (closed_pending_origin expression key state pending).probe_absence facts.coherent

end MicroCFTA.InternedPendingOrigins
