import MicroCFTA.SourceSynthesisUniverseColdReadback

/-!
# Actual cold universe callback frames

The original construction supplies both probes, the reservation miss, and
the fresh body callback. Each frame grows into the completed universe heap.
The reserved reference and the callback input state are the actual source
reservation. No completed callback is supplied by the caller.
-/
namespace MicroCFTA.SourceSynthesisUniverseColdFrames
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome request finish)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisTypeSyntax

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- Original universe construction derives its exact probe, reservation, and fresh-body frames. -/
theorem allTypes_cold_frames (top : Guard) (catalog : List (String × Nat)) :
    ∃ entry body depth ordinary originalHeap afterDepth afterOrdinary afterBody,
      let allocated : InternedConstructorTemplates.State String Guard :=
        {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2}
      InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] empty =
        .done (.mu entry body depth ordinary) originalHeap ∧
      Facts originalHeap ∧ Available originalHeap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body ∧
      InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) [] .depth empty =
        .done depth afterDepth ∧
      InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth =
        .done ordinary afterOrdinary ∧
      InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []
        (.interned entry.identity) allocated = .done body afterBody ∧
      entry = (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1 ∧
      afterOrdinary.nodes.table (muKey depth ordinary) = none ∧
      Facts afterDepth ∧ Facts afterOrdinary ∧ Facts allocated ∧
      Available allocated (.reference (.interned entry.identity)) ∧ Facts afterBody ∧
      originalHeap = {afterBody with nodeRecords := keepFirst afterBody.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary)} ∧
      Grows afterDepth originalHeap ∧ Grows afterOrdinary originalHeap ∧
      Grows allocated originalHeap ∧ Grows afterBody originalHeap := by
  obtain ⟨oldEntry, oldBody, oldDepth, oldOrdinary, originalHeap,
      coldDone, finalFacts, coldAvailable, _oldShape, _oldKey, _oldTable, _oldRecord, _oldClosed⟩ :=
    SourceSynthesisUniverseColdReadback.allTypes_cold_mu top catalog
  obtain ⟨depth, afterDepth, ordinary, afterOrdinary, depthDone, ordinaryDone,
      ordinaryFacts, _depthAvailable, _ordinaryAvailable, missing, expanded⟩ :=
    SourceSynthesisUniverseColdProbe.allTypes_cold_probes top catalog
  have requested : request true depth ordinary
      (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []) afterOrdinary =
      .done (.mu oldEntry oldBody oldDepth oldOrdinary) originalHeap :=
    expanded.symm.trans coldDone
  obtain ⟨body, afterBody, bodyDone, _bodyMissing, finished, finalState⟩ :=
    InternedFreshOrdinaryReadback.request_miss true (allTypesBody top catalog) []
      depth ordinary afterOrdinary ordinaryFacts.coherent missing
      (.mu oldEntry oldBody oldDepth oldOrdinary) originalHeap requested
  let entry := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1
  let allocated : InternedConstructorTemplates.State String Guard :=
    {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2}
  have allocatedFacts : Facts allocated :=
    reserve_facts (muKey depth ordinary) afterOrdinary ordinaryFacts
  have freshAvailable : Available allocated (.reference (.interned entry.identity)) :=
    (InternedConstructionProvenance.reserve_available (muKey depth ordinary) afterOrdinary
      ordinaryFacts.coherent ordinaryFacts.cached).2
  obtain ⟨shaped, _shapedFinal, shapedDone, shapedShape, _shapedFacts, _shapedAvailable⟩ :=
    SourceSynthesisUniverseBody.callback_readback top catalog (.interned entry.identity)
      allocated allocatedFacts freshAvailable
  have sameBody : body = shaped := (Outcome.done.inj (bodyDone.symm.trans shapedDone)).1
  have bodyShape : SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body :=
    sameBody.symm ▸ shapedShape
  have sameMu : (Value.mu oldEntry oldBody oldDepth oldOrdinary) = .mu entry body depth ordinary :=
    finished.trans
      (SourceSynthesisUniverseColdReadback.finish_shaped_mu top catalog entry body depth ordinary bodyShape)
  have actualDone : InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] empty =
      .done (.mu entry body depth ordinary) originalHeap := sameMu ▸ coldDone
  have actualAvailable : Available originalHeap (.mu entry body depth ordinary) := sameMu ▸ coldAvailable
  have depthChecked := InternedFreshOrdinaryFacts.callback_verified (allTypesBody top catalog) [] .depth
    empty empty_facts (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact InternedNestedProvenance.depth_available empty)
  have depthFacts : Facts afterDepth := by
    simpa only [depthDone, Outcome.state] using depthChecked.facts
  have ordinaryChecked := InternedFreshOrdinaryFacts.callback_verified (allTypesBody top catalog) []
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthFacts (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact InternedNestedProvenance.ordinary_available afterDepth _)
  have ordinaryGrowth : Grows afterDepth afterOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.growth
  have allocatedGrowth : Grows afterOrdinary allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have bodyChecked := InternedFreshOrdinaryFacts.callback_verified (allTypesBody top catalog) []
    (.interned entry.identity) allocated allocatedFacts (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact freshAvailable)
  dsimp only [entry, allocated] at bodyDone bodyChecked
  have bodyFacts : Facts afterBody := by
    simpa only [bodyDone, Outcome.state] using bodyChecked.facts
  have bodyGrowth : Grows allocated afterBody := by
    simpa only [bodyDone, Outcome.state] using bodyChecked.growth
  have publishedGrowth : Grows afterBody originalHeap := by
    rw [finalState]
    exact ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩
  have allocatedFinal : Grows allocated originalHeap := grows_trans bodyGrowth publishedGrowth
  have ordinaryFinal : Grows afterOrdinary originalHeap := grows_trans allocatedGrowth allocatedFinal
  exact ⟨entry, body, depth, ordinary, originalHeap, afterDepth, afterOrdinary, afterBody,
    actualDone, finalFacts, actualAvailable, bodyShape, depthDone, ordinaryDone, bodyDone, rfl, missing,
    depthFacts, ordinaryFacts, allocatedFacts, freshAvailable, bodyFacts, finalState,
    grows_trans ordinaryGrowth ordinaryFinal, ordinaryFinal, allocatedFinal, publishedGrowth⟩

end MicroCFTA.SourceSynthesisUniverseColdFrames
