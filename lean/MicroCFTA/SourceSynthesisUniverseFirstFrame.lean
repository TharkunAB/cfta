import MicroCFTA.SourceSynthesisUniverseColdReadback
import MicroCFTA.SourceSynthesisUniverseResidentRows

/-!
# First universe construction in the actual incoming heap

Earlier ordinary construction can allocate identities before the universe.
The incoming Mu-free history derives a fresh reservation after both probes.
The actual reservation determines the universe identity and its body rows.
All three resident row packets remain in the actual completed heap.
These are internal state conditions for the original-prefix induction.
-/
namespace MicroCFTA.SourceSynthesisUniverseFirstFrame
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome request)
open InternedBinderProtocol (Reference NodeKey)
open InternedRecordCoherence (Covered)
open InternedShallowHeap (NoNewMu noNewMu_trans)
open SourceSynthesisTypeSyntax
open SourceSynthesisUniverseResidentRows (Rows)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- The first actual universe call derives its identity and probe rows in a Mu-free incoming heap. -/
theorem allTypes_first_frame (top : Guard) (catalog : List (String × Nat))
    (initial : InternedConstructorTemplates.State String Guard) (facts : Facts initial)
    (covered : Covered [] initial) (muFree : NoNewMu empty initial) :
    ∃ entry body depth ordinary final,
      InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] initial =
        .done (.mu entry body depth ordinary) final ∧
      Facts final ∧ Available final (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body ∧
      Rows top catalog (.interned entry.identity) body final ∧
      Rows top catalog .depth depth final ∧
      Rows top catalog (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary final ∧
      Grows initial final ∧ Cache.Extends initial.nodes.issued final.nodes.issued := by
  obtain ⟨value, final, built⟩ := SourceSynthesisUniverseNativeInput.allTypes_complete top catalog []
    initial facts.coherent.valid covered
  have checked := InternedFreshOrdinaryFacts.build_verified (allTypes top catalog) [] initial facts
    (by intro value member; cases member)
  have finalFacts : Facts final := by simpa only [built, Outcome.state] using checked.facts
  have available : Available final value := checked.result value final built
  have finalGrowth : Grows initial final := by simpa only [built, Outcome.state] using checked.growth
  have finalHistory : Cache.Extends initial.nodes.issued final.nodes.issued := by
    simpa only [built, Outcome.state] using checked.history
  obtain ⟨depth, afterDepth, depthDone, _depthShape, depthFacts, _depthAvailable, depthRows⟩ :=
    SourceSynthesisUniverseBody.callback_readback_with_rows top catalog .depth initial facts
      (InternedNestedProvenance.depth_available initial)
  have depthPacket : Rows top catalog .depth depth afterDepth := depthRows
  have depthCovered := InternedFreshOrdinaryCoverage.callback_covered (allTypesBody top catalog) []
    .depth initial facts.coherent.valid covered depth afterDepth depthDone
  obtain ⟨ordinary, afterOrdinary, ordinaryDone, _ordinaryShape, ordinaryFacts,
      _ordinaryAvailable, ordinaryRows⟩ :=
    SourceSynthesisUniverseBody.callback_readback_with_rows top catalog
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthFacts
      (InternedNestedProvenance.ordinary_available afterDepth _)
  have ordinaryPacket : Rows top catalog
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary afterOrdinary := ordinaryRows
  have ordinaryCovered := InternedFreshOrdinaryCoverage.callback_covered (allTypesBody top catalog) []
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth
    depthFacts.coherent.valid depthCovered ordinary afterOrdinary ordinaryDone
  have binderFree := SourceSynthesisUniverseNativeInput.allTypesBody_binderFree top catalog
  have firstMuFree : NoNewMu initial afterDepth := by
    simpa only [depthDone, Outcome.state] using
      SourceSynthesisUniverseColdProbe.binderFree_callback_noNewMu (allTypesBody top catalog) []
        .depth initial binderFree
  have secondMuFree : NoNewMu afterDepth afterOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using
      SourceSynthesisUniverseColdProbe.binderFree_callback_noNewMu (allTypesBody top catalog) []
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth binderFree
  have missing := SourceSynthesisUniverseColdProbe.empty_mu_key_absent afterOrdinary ordinaryFacts
    ordinaryCovered (noNewMu_trans muFree (noNewMu_trans firstMuFree secondMuFree)) depth ordinary
  have expanded : InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] initial =
      (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) [] .depth initial).bind
        (fun depth afterDepth =>
          (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []
            (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth).bind
            (fun ordinary afterOrdinary => request true depth ordinary
              (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []) afterOrdinary)) := by
    change InternedFreshOrdinaryConstruction.build (.binder true (allTypesBody top catalog)) [] initial = _
    rw [InternedFreshOrdinaryConstruction.build]
    rfl
  have requested : request true depth ordinary
      (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []) afterOrdinary = .done value final := by
    rw [expanded, depthDone] at built
    simpa only [Outcome.bind, ordinaryDone] using built
  obtain ⟨body, afterBody, bodyDone, _bodyMissing, finished, finalState⟩ :=
    InternedFreshOrdinaryReadback.request_miss true (allTypesBody top catalog) [] depth ordinary
      afterOrdinary ordinaryFacts.coherent missing value final requested
  let entry := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1
  let allocated : InternedConstructorTemplates.State String Guard :=
    {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2}
  have allocatedFacts : Facts allocated := reserve_facts (muKey depth ordinary) afterOrdinary ordinaryFacts
  have freshAvailable : Available allocated (.reference (.interned entry.identity)) :=
    (InternedConstructionProvenance.reserve_available (muKey depth ordinary) afterOrdinary
      ordinaryFacts.coherent ordinaryFacts.cached).2
  obtain ⟨shaped, shapedFinal, shapedDone, shapedShape, _shapedFacts, _shapedAvailable, shapedRows⟩ :=
    SourceSynthesisUniverseBody.callback_readback_with_rows top catalog (.interned entry.identity)
      allocated allocatedFacts freshAvailable
  have sameBody : body = shaped := (Outcome.done.inj (bodyDone.symm.trans shapedDone)).1
  have sameFinal : afterBody = shapedFinal := (Outcome.done.inj (bodyDone.symm.trans shapedDone)).2
  have bodyShape : SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body :=
    sameBody.symm ▸ shapedShape
  have bodyPacket : Rows top catalog (.interned entry.identity) body afterBody := by
    rw [sameBody, sameFinal]
    exact shapedRows
  have sameMu : value = .mu entry body depth ordinary :=
    finished.trans (SourceSynthesisUniverseColdReadback.finish_shaped_mu top catalog
      entry body depth ordinary bodyShape)
  have actualBuilt : InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] initial =
      .done (.mu entry body depth ordinary) final := sameMu ▸ built
  have actualAvailable : Available final (.mu entry body depth ordinary) := sameMu ▸ available
  have ordinaryChecked := InternedFreshOrdinaryFacts.callback_verified (allTypesBody top catalog) []
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthFacts (by
      intro item member
      have same := List.mem_singleton.mp member
      subst item
      exact InternedNestedProvenance.ordinary_available afterDepth _)
  have ordinaryGrowth : Grows afterDepth afterOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.growth
  have allocatedGrowth : Grows afterOrdinary allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have bodyChecked := InternedFreshOrdinaryFacts.callback_verified (allTypesBody top catalog) []
    (.interned entry.identity) allocated allocatedFacts (by
      intro item member
      have same := List.mem_singleton.mp member
      subst item
      exact freshAvailable)
  dsimp only [entry, allocated] at bodyDone bodyChecked
  have bodyGrowth : Grows allocated afterBody := by
    simpa only [bodyDone, Outcome.state] using bodyChecked.growth
  have publishedGrowth : Grows afterBody final := by
    rw [finalState]
    exact ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩
  have ordinaryFinal : Grows afterOrdinary final :=
    grows_trans allocatedGrowth (grows_trans bodyGrowth publishedGrowth)
  exact ⟨entry, body, depth, ordinary, final, actualBuilt, finalFacts, actualAvailable, bodyShape,
    bodyPacket.grows publishedGrowth, depthPacket.grows (grows_trans ordinaryGrowth ordinaryFinal),
    ordinaryPacket.grows ordinaryFinal, finalGrowth, finalHistory⟩

end MicroCFTA.SourceSynthesisUniverseFirstFrame
