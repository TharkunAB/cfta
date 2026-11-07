import MicroCFTA.SourceSynthesisUniverseProductProbe
import MicroCFTA.SourceSynthesisUniverseReferenceIdentityJoin
import MicroCFTA.SourceSynthesisUniverseBodyExactFree
import MicroCFTA.SourceSynthesisUniverseColdResidentRows
import MicroCFTA.SourceSynthesisUniverseTopConjunction
import MicroCFTA.SourceRecursiveIntersectionKernelCoverage
import MicroCFTA.SourceRecursiveIntersectionKernelStability

/-!
# Exact open-universe identity from original synthesis inputs

The cold constructor supplies the original universe and its resident rows.
The actual body product supplies the transformed rows. Both product probes
return the original probe records. The outer binder then reuses the original
universe record. The complete request retains its final heap and domain cache.
Thirteen recursive levels suffice for this request. Larger fuel gives the
same result and machine. This is not a bound on total work.
-/
namespace MicroCFTA.SourceSynthesisUniverseReferenceIdentityInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference)
open InternedRecordCoherence (Covered)
open InternedEdgeResidency (nodeEdges)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original library and query data derive the exact open-universe result and both final caches. -/
theorem typesOf_reference_identity (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap final,
      let initial : Machine String Guard := ⟨heap, Cache.emptyState⟩
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      SourceRecursiveIntersectionKernel.Valid initial ∧
      execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension initial final ∧
      Available final.heap (.mu entry body depth ordinary) ∧ Covered [] final.heap ∧
      (∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (13 + extra) IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final) := by
  let catalog := SourceSynthesisFirstOrderConstruction.constructorCatalog lib query
  obtain ⟨entry, body, depth, ordinary, heap, built, facts, universeAvailable, shape,
      bodyRowsPacket, depthRows, ordinaryRows, bodyAvailable, depthAvailable, ordinaryAvailable⟩ :=
    SourceSynthesisUniverseColdResidentRows.allTypes_cold_rows top catalog
  have bodyData := bodyRowsPacket
  obtain ⟨b, _marker, arrow, rest, bodyEq, _⟩ := bodyData
  let bodyRows := canonicalEdges (arrow :: rest)
  let initial : Machine String Guard := ⟨heap, Cache.emptyState⟩
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, Cache.empty_valid⟩
  have nodeAvailable : Available initial.heap
      (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    rw [← bodyEq]
    exact universeAvailable
  have nodeShape : SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity)
      (.node b bodyRows 0 [.interned entry.identity]) := by
    rw [← bodyEq]
    exact shape
  obtain ⟨product, final, productEntry, targets, _m, _markerRow, bodyDone, finalValid, growth,
      productAvailable, _prepared, productEq, aligned, productResident, _live, _tops, _kinds,
      _markerRead, _markerAvailable, _nodeReplay⟩ :=
    SourceSynthesisUniverseBodyExactFree.node_target_readback top catalog entry b bodyRows depth ordinary
      top SourceEqualityPCSNativeEdge.conjoin SourceSynthesisUniverseTopConjunction.native_conjoin_top
      initial facts Cache.empty_valid nodeAvailable nodeShape
  have entered := SourceSynthesisUniverseSecondDomain.second_checked entry b bodyRows depth ordinary
    initial facts Cache.empty_valid nodeAvailable
  have totalGrowth : Extension initial final := entered.2.1.trans growth
  have finalUniverse : Available final.heap (.mu entry body depth ordinary) :=
    totalGrowth.available _ universeAvailable
  have finalBody := totalGrowth.available _ bodyAvailable
  have finalDepth := totalGrowth.available _ depthAvailable
  have finalOrdinary := totalGrowth.available _ ordinaryAvailable
  have finalBodyRows := bodyRowsPacket.grows totalGrowth.heap
  have finalDepthRows := depthRows.grows totalGrowth.heap
  have finalOrdinaryRows := ordinaryRows.grows totalGrowth.heap
  have alignedSource : Language.All₂ (SourceSynthesisUniverseRowTransform.Readback top entry.identity)
      (nodeEdges body) targets := by simpa only [bodyEq, nodeEdges] using aligned
  have productNodeAvailable : Available final.heap
      (.node productEntry (canonicalEdges targets) 0
        [.intersection (pair entry.identity entry.identity).1 (pair entry.identity entry.identity).2]) := by
    rw [← productEq]
    exact productAvailable
  have depthReplay := SourceSynthesisUniverseProductProbe.execute_probe top catalog entry.identity .depth
    body productEntry targets depth final.heap finalValid.1 finalBody productNodeAvailable finalDepth
    finalBodyRows finalDepthRows alignedSource productResident
  have ordinaryReplay := SourceSynthesisUniverseProductProbe.execute_probe top catalog entry.identity
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) body productEntry targets ordinary
    final.heap finalValid.1 finalBody productNodeAvailable finalOrdinary finalBodyRows finalOrdinaryRows
    alignedSource productResident
  let pending : Reference := .intersection (pair entry.identity entry.identity).1
    (pair entry.identity entry.identity).2
  have depthCallback : SourceRecursiveIntersectionMaybeMu.callback pending product .depth final.heap =
      .done depth final.heap := by rw [productEq]; exact depthReplay.2
  have ordinaryCallback : SourceRecursiveIntersectionMaybeMu.callback pending product
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) final.heap =
      .done ordinary final.heap := by rw [productEq]; exact ordinaryReplay.2
  obtain ⟨_, table, record⟩ := SourceSynthesisUniverseNativeInput.available_mu_key_readback
    final.heap finalValid.1 entry body depth ordinary finalUniverse
  have finished := SourceSynthesisUniverseColdReadback.finish_shaped_mu
    top catalog entry body depth ordinary shape
  have pendingMember : pending ∈ product.free := by simp only [productEq, Value.free, List.mem_singleton, pending]
  dsimp only [pending] at depthCallback ordinaryCallback pendingMember
  have outerDone : SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity)
      product final.heap = .done (.mu entry body depth ordinary) final.heap := by
    simp only [SourceRecursiveIntersectionMaybeMu.maybeMu, ite_eq_left pendingMember,
      SourceRecursiveIntersectionMaybeMu.construct, depthCallback, Outcome.bind, ordinaryCallback,
      InternedNestedConstruction.request, table, record, finished]
  obtain ⟨m, markerRow, _arrow, _markerRead, leaf, markerTop, markerAvailable, _member,
      _arrowChildren, _arrowKey, _rowKinds, bodyTop, bodyChildren⟩ :=
    SourceSynthesisUniverseBodyEvidence.of_shape top catalog entry b bodyRows depth ordinary
      initial.heap nodeAvailable nodeShape
  have outerNode : SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity)
      product final.heap = .done (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary)
        final.heap := by rw [← bodyEq]; exact outerDone
  have nodeDone := SourceSynthesisUniverseReferenceIdentityJoin.execute_reference_identity
    entry b m bodyRows markerRow depth ordinary top SourceEqualityPCSNativeEdge.conjoin top
    SourceSynthesisUniverseTopConjunction.native_conjoin_top initial facts Cache.empty_valid nodeAvailable
    markerAvailable leaf markerTop bodyTop bodyChildren product final bodyDone outerNode
  have done : execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
        .done (.mu entry body depth ordinary) final := by rw [bodyEq]; exact nodeDone
  have referenceAvailable : Available initial.heap (.reference (.interned entry.identity)) := by
    apply reference_available
    intro identity member
    apply bodyAvailable.issued identity
    simpa only [bodyEq, Value.free] using member
  have incomingCovered := InternedFreshOrdinaryCoverage.closed_covered
    (SourceSynthesisFirstOrderConstruction.typesOf lib query) (.mu entry body depth ordinary) heap built
  have finalCovered : Covered [] final.heap :=
    SourceRecursiveIntersectionKernelCoverage.execute_covered (pending := []) top SourceEqualityPCSNativeEdge.conjoin
      13 IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity)) (.mu entry body depth ordinary)
      initial initialValid (empty_domain initial) referenceAvailable universeAvailable incomingCovered
      (.mu entry body depth ordinary) final done
  have closed : (Value.mu entry body depth ordinary).free = [] := by simp [Value.free, bodyEq]
  have allExtra : ∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (13 + extra)
      IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity)) (.mu entry body depth ordinary)
      initial = .done (.mu entry body depth ordinary) final := by
    intro extra
    exact (SourceRecursiveIntersectionKernel.execute_stable top SourceEqualityPCSNativeEdge.conjoin
      13 extra IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity))
      (.mu entry body depth ordinary) initial (by rw [done]; trivial)).trans done
  exact ⟨entry, body, depth, ordinary, heap, final, built, facts, universeAvailable, shape, closed,
    initialValid, done, finalValid, totalGrowth, finalUniverse, finalCovered, allExtra⟩

end MicroCFTA.SourceSynthesisUniverseReferenceIdentityInput
