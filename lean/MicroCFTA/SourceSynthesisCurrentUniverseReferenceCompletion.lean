import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourceSynthesisUniverseInnerMu
import MicroCFTA.SourceSynthesisUniverseTopConjunction
import MicroCFTA.SourceRecursiveIntersectionKernelCoverage
import MicroCFTA.SourceRecursiveIntersectionKernelStability
import MicroCFTA.SourceRecursiveIntersectionKernelScope

/-!
# Actual open-universe completion from the current source heap

An observed stored Mu belongs to the same completed current root build.
Its actual rows supply the real native body and reference requests.
The complete source heap lets the final optional binder finish.
The result retains both caches and all earlier source records.
This theorem does not identify the returned value with the original Mu.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseReferenceCompletion
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (NodeKey)
open InternedRecordCoherence (Covered)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (first firstState second secondState)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The actual source Mu derives a closed native return and the complete final machine. -/
theorem current_stored_universe_reference_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : heap.nodeRecords key = some (.mu entry body depth ordinary))
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (cacheValid : Cache.Valid domains) :
    let initial : Machine Symbol Guard := ⟨heap, domains⟩
    ∃ (value : Value Symbol Guard) (final : Machine Symbol Guard),
      SourceRecursiveIntersectionKernel.Valid initial ∧
      Available initial.heap (.mu entry body depth ordinary) ∧
      execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap final.heap ∧
      Extension initial final ∧ Covered [] final.heap ∧ Available final.heap value ∧ value.free = [] ∧
      Available final.heap (.mu entry body depth ordinary) ∧ Available final.heap rootValue ∧
      final.heap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      (∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (13 + extra) IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial = .done value final) := by
  let initial : Machine Symbol Guard := ⟨heap, domains⟩
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have facts : Facts heap := by
    simpa only [built, Outcome.state] using checked.facts
  have rootAvailable : Available heap rootValue := checked.result rootValue heap built
  have universeAvailable : Available heap (.mu entry body depth ordinary) := facts.cached.nodes key _ stored
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, cacheValid⟩
  have incomingCovered : Covered [] heap :=
    InternedFreshOrdinaryCoverage.closed_covered (ordinarySymbols whole) rootValue heap built
  obtain ⟨b, marker, arrow, rows, bodyEq, markerRead, _arrowChildren, _arrowKey,
      _aligned, _markerClosed, markerAvailable, kinds, _retained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue heap built key entry body depth ordinary stored
  let bodyRows := canonicalEdges (arrow :: rows)
  obtain ⟨m, markerRow, markerEq, leaf, markerKey⟩ := markerRead
  have nativeUniverse : Available initial.heap
      (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    simpa only [bodyEq, bodyRows] using universeAvailable
  have nativeMarker : Available initial.heap (.node m [markerRow] 0 []) := markerEq ▸ markerAvailable
  have markerTop : markerRow.entry.key.constraint = top := congrArg EdgeKey.constraint markerKey
  have bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top := fun row member => (kinds row member).1
  have bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned entry.identity) := by
    intro row member child included
    simpa only [markerEq] using (kinds row member).2 child included
  have bodyAvailable : Available initial.heap (.node b bodyRows 0 [.interned entry.identity]) :=
    nativeUniverse.children _ (by simp [InternedProbeProvenance.children])
  have referenceAvailable : Available initial.heap (.reference (.interned entry.identity)) := by
    apply reference_available
    intro identity member
    apply bodyAvailable.issued identity
    simpa only [Value.free] using member
  obtain ⟨product, middle, done9, _innerUnused, done11, middleValid, growth,
      productAvailable, prepared, _free⟩ :=
    SourceSynthesisUniverseInnerMu.execute_body_reference_complete entry b m bodyRows markerRow depth ordinary
      top SourceEqualityPCSNativeEdge.conjoin top SourceSynthesisUniverseTopConjunction.native_conjoin_top
      initial facts cacheValid nativeUniverse nativeMarker leaf markerTop bodyTop bodyChildren
  have entered := SourceSynthesisUniverseSecondDomain.second_checked entry b bodyRows depth ordinary
    initial facts cacheValid nativeUniverse
  have middleCovered : Covered [] middle.heap :=
    SourceRecursiveIntersectionKernelCoverage.execute_covered (pending := []) top SourceEqualityPCSNativeEdge.conjoin
      9 (second entry b bodyRows depth ordinary initial).1
      (.node b bodyRows 0 [.interned entry.identity]) (.node b bodyRows 0 [.interned entry.identity])
      (secondState entry b bodyRows depth ordinary initial) entered.1 entered.2.2
      bodyAvailable bodyAvailable incomingCovered product middle done9
  obtain ⟨value, after, completed, afterFacts, available, heapGrowth, issuedGrowth⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete (pair entry.identity entry.identity) product middle.heap
      middleValid.1 productAvailable middleCovered prepared
  let final : Machine Symbol Guard := {middle with heap := after}
  have lastGrowth : Extension middle final := ⟨heapGrowth, issuedGrowth, extends_refl _⟩
  have totalGrowth : Extension initial final := growth.trans lastGrowth
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := ⟨afterFacts, middleValid.2⟩
  have finalCovered : Covered [] final.heap :=
    SourceRecursiveIntersectionMaybeMu.maybeMu_covered (pair entry.identity entry.identity) product middle.heap
      middleValid.1.coherent.valid middleCovered value after completed
  have nativeDone : execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned entry.identity)) (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary)
      initial = .done value final := by
    rw [show 13 = 11 + 2 from rfl, SourceSynthesisUniverseReferenceControl.execute_referenceMu]
    change (execute top SourceEqualityPCSNativeEdge.conjoin 11 (first entry b bodyRows depth ordinary initial).1
      (.node b bodyRows 0 [.interned entry.identity]) (.reference (.interned entry.identity))
      (firstState entry b bodyRows depth ordinary initial)).bind
        (fun result after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity) result after.heap) after) = _
    simp only [done11, Result.bind, completed, construction, final]
  have done : execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial = .done value final := by
    simpa only [bodyEq, bodyRows] using nativeDone
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed (ordinarySymbols whole) rootValue heap built
  have scopeResult := SourceRecursiveIntersectionScopeCalls.execute_scoped top SourceEqualityPCSNativeEdge.conjoin
    13 IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity)) (.mu entry body depth ordinary)
    initial initialValid (empty_domain initial) referenceAvailable universeAvailable semantic value final done
  have closed : value.free = [] := SourceRecursiveIntersectionResultScope.empty_scope value scopeResult.2
  refine ⟨value, final, initialValid, universeAvailable, done, finalValid, scopeResult.1,
    totalGrowth, finalCovered, available, closed, totalGrowth.available _ universeAvailable,
    totalGrowth.available _ rootAvailable, totalGrowth.heap.nodeRecords key _ stored, ?_⟩
  intro extra
  exact (SourceRecursiveIntersectionKernel.execute_stable top SourceEqualityPCSNativeEdge.conjoin
    13 extra IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity))
    (.mu entry body depth ordinary) initial (by rw [done]; trivial)).trans done


end MicroCFTA.SourceSynthesisCurrentUniverseReferenceCompletion
