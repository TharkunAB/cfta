import MicroCFTA.InternedPendingEncounter
import MicroCFTA.InternedBoundaryAge

/-!
# The exact old-probe obligation of an unrestricted pending source call

A pending call captures its active ancestor's actual fresh reference.
Both of its completed probe results already exist before that reference
was allocated. The source reservation and complete cache readback derive
these facts without an assumed relation between callback executions.
-/
namespace MicroCFTA.InternedPendingOldCall
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedProbeProvenance InternedFreshProbeKeys InternedNestedFacts InternedNestedProvenance
open InternedPendingOrigins InternedPendingEncounter InternedNestedMissReadback
open InternedNodeIdentityFootprint InternedBoundaryAtoms
open InternedBinderProtocol (NodeKey)

/-- Every actual pending encounter captures the new ancestor name while both completed probes are old complete records. -/
theorem encounter_old [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard)
    (encounter : Encounter key final) :
    ∃ body environment cut before depth afterDepth ordinary,
      Coherent cut ∧ Facts before ∧ Facts afterDepth ∧ Facts final ∧ Values before environment ∧
      Grows cut before ∧ Grows before afterDepth ∧ Grows afterDepth final ∧
      cut.nodes.table key = none ∧ before.nodes.table key = some (Cache.intern cut.nodes key).1 ∧
      .reference (.interned cut.nodes.next) ∈ environment ∧
      callback body environment .depth before = .done depth afterDepth ∧
      callback body environment (.uninterned depth.depth) afterDepth = .done ordinary final ∧
      Available cut depth ∧ Available cut ordinary ∧ key = muKey depth ordinary ∧ IsPending key final := by
  obtain ⟨body, environment, before, depth, afterDepth, ordinary, beforeFacts, inputs, origin,
      captured, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable, actualKey, pending⟩ := encounter
  obtain ⟨cut, oldDepth, oldOrdinary, oldKey, missing, cutCoherent, oldDepthAvailable, oldOrdinaryAvailable,
      cutGrowth, installed⟩ := origin
  obtain ⟨entry, present, member⟩ := captured
  have entrySame : entry = (Cache.intern cut.nodes key).1 := Option.some.inj (present.symm.trans installed)
  have capturedName : .reference (.interned cut.nodes.next) ∈ environment := by
    rw [entrySame, intern_miss_identity cut.nodes key missing] at member
    exact member
  have depthVerified := callback_verified body environment .depth before beforeFacts inputs (depth_available before)
  have depthFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using depthVerified.facts
  have depthGrowth : Grows before afterDepth := by simpa only [depthDone, Outcome.state] using depthVerified.growth
  have afterInputs := values_after depthVerified inputs depthDone
  have ordinaryVerified := callback_verified body environment (.uninterned depth.depth) afterDepth depthFacts afterInputs
    (ordinary_available afterDepth depth.depth)
  have finalFacts : Facts final := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.facts
  have ordinaryGrowth : Grows afterDepth final := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.growth
  have completeGrowth := grows_trans cutGrowth (grows_trans depthGrowth ordinaryGrowth)
  have references : depth.referenceOf = oldDepth.referenceOf ∧ ordinary.referenceOf = oldOrdinary.referenceOf := by
    simpa only [muKey, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq] using actualKey.symm.trans oldKey
  have depthSame := resident_reference_injective final finalFacts.coherent depth oldDepth depthAvailable.resident
    (resident_grows cut final completeGrowth oldDepth oldDepthAvailable.resident) references.1
  have ordinarySame := resident_reference_injective final finalFacts.coherent ordinary oldOrdinary ordinaryAvailable.resident
    (resident_grows cut final completeGrowth oldOrdinary oldOrdinaryAvailable.resident) references.2
  exact ⟨body, environment, cut, before, depth, afterDepth, ordinary,
    cutCoherent, beforeFacts, depthFacts, finalFacts, inputs, cutGrowth, depthGrowth, ordinaryGrowth, missing, installed,
    capturedName, depthDone, ordinaryDone, depthSame.symm ▸ oldDepthAvailable, ordinarySame.symm ▸ oldOrdinaryAvailable, actualKey, pending⟩

/-- Unrestricted closed source execution exposes the same exact old-probe callback obligation. -/
theorem closed_old_call [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (stopped : build expression [] empty = .pending key final) :
    ∃ body environment cut before depth afterDepth ordinary,
      Coherent cut ∧ Facts before ∧ Facts afterDepth ∧ Facts final ∧ Values before environment ∧
      Grows cut before ∧ Grows before afterDepth ∧ Grows afterDepth final ∧
      cut.nodes.table key = none ∧ before.nodes.table key = some (Cache.intern cut.nodes key).1 ∧
      .reference (.interned cut.nodes.next) ∈ environment ∧
      callback body environment .depth before = .done depth afterDepth ∧
      callback body environment (.uninterned depth.depth) afterDepth = .done ordinary final ∧
      Available cut depth ∧ Available cut ordinary ∧ key = muKey depth ordinary ∧ IsPending key final :=
  encounter_old key final (closed_encounter expression key final stopped)

/-- Earlier complete probe records exclude all later reference and Mu boundaries. -/
theorem old_probe_boundaries (cut : State Symbol Guard) (coherent : Coherent cut)
    (depth ordinary : Value Symbol Guard) (depthAvailable : Available cut depth) (ordinaryAvailable : Available cut ordinary)
    (identity : Nat) (new : cut.nodes.next ≤ identity) :
    (.ref (.interned identity) ∉ atoms depth ∧ .mu identity ∉ atoms depth) ∧
      (.ref (.interned identity) ∉ atoms ordinary ∧ .mu identity ∉ atoms ordinary) :=
  ⟨InternedBoundaryAge.old_absent depth cut.nodes.next (available_below cut coherent depth depthAvailable) identity new,
    InternedBoundaryAge.old_absent ordinary cut.nodes.next (available_below cut coherent ordinary ordinaryAvailable) identity new⟩

end MicroCFTA.InternedPendingOldCall
