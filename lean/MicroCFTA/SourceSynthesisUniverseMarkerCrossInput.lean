import MicroCFTA.SourceSynthesisUniverseMarkerInput
import MicroCFTA.SourceSynthesisUniverseMarkerReference

/-!
# Original synthesis inputs supply both marker/reference cross-children

The original Library and Query data construct the default type universe.
Its actual body supplies the closed marker and the issued Mu reference.
Both source requests start in the same second machine. This machine comes
from the two actual domain allocations after construction from empty caches.
Each request completes with a closed available value and valid heap facts.
Marker identity, catalog membership, and the whole body product are separate.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerCrossInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniverseBodyReferenceControl (second secondState)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original inputs derive both actual D2 cross-child completions and their input invariants. -/
theorem typesOf_marker_cross_complete (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap bodyEntry bodyRows marker forward forwardFinal backward backwardFinal,
      let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
      let entered := secondState entry bodyEntry bodyRows depth ordinary initial
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      SourceSynthesisUniverseBody.RowReadback "(->)" top [] marker ∧ marker ∈ children body ∧
      SourceRecursiveIntersectionKernel.Valid initial ∧ SourceRecursiveIntersectionKernel.Valid entered ∧
      Available entered.heap (.mu entry body depth ordinary) ∧ Available entered.heap marker ∧
      Available entered.heap (.reference (.interned entry.identity)) ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 7
        (second entry bodyEntry bodyRows depth ordinary initial).1
        marker (.reference (.interned entry.identity)) entered = .done forward forwardFinal ∧
      Facts forwardFinal.heap ∧ Available forwardFinal.heap forward ∧ forward.free = [] ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 8
        (second entry bodyEntry bodyRows depth ordinary initial).1
        (.reference (.interned entry.identity)) marker entered = .done backward backwardFinal ∧
      Facts backwardFinal.heap ∧ Available backwardFinal.heap backward ∧ backward.free = [] := by
  obtain ⟨entry, body, depth, ordinary, heap, built, facts, universeAvailable, shape, closed⟩ :=
    SourceSynthesisUniverseColdReadback.typesOf_cold_mu lib query
  obtain ⟨bodyEntry, bodyRows, markerEntry, markerEdge, marker, bodyEq, markerEq,
      markerRead, markerChildren, member, markerAvailable⟩ :=
    SourceSynthesisUniverseMarkerInput.shape_marker_available top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
      entry body depth ordinary heap universeAvailable shape
  let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
  let entered := secondState entry bodyEntry bodyRows depth ordinary initial
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, Cache.empty_valid⟩
  have enteredValid : SourceRecursiveIntersectionKernel.Valid entered :=
    ⟨facts, SourceSynthesisUniverseMarkerReference.second_valid entry bodyEntry bodyRows depth ordinary
      initial Cache.empty_valid⟩
  have bodyAvailable : Available heap body := universeAvailable.children body (by simp [children])
  have referenceAvailable : Available heap (.reference (.interned entry.identity)) := by
    apply reference_available
    intro identity included
    apply bodyAvailable.issued identity
    simpa only [bodyEq, Value.free] using included
  have markerNodeAvailable : Available initial.heap (.node markerEntry [markerEdge] 0 []) := by
    rw [← markerEq]
    exact markerAvailable
  have universeNodeAvailable : Available initial.heap
      (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    rw [← bodyEq]
    exact universeAvailable
  have leaves : ∀ row ∈ [markerEdge], row.children = [] := by
    intro row included
    have same := List.mem_singleton.mp included
    subst row
    exact markerChildren
  obtain ⟨forward, forwardFinal, forwardDone, forwardFacts, forwardAvailable, forwardClosed⟩ :=
    SourceSynthesisUniverseMarkerReference.marker_reference_complete entry bodyEntry markerEntry
      bodyRows [markerEdge] 0 depth ordinary top SourceEqualityPCSNativeEdge.conjoin initial facts
      Cache.empty_valid universeNodeAvailable markerNodeAvailable leaves
  obtain ⟨backward, backwardFinal, backwardDone, backwardFacts, backwardAvailable, backwardClosed⟩ :=
    SourceSynthesisUniverseMarkerReference.reference_marker_complete entry bodyEntry markerEntry
      bodyRows [markerEdge] 0 depth ordinary top SourceEqualityPCSNativeEdge.conjoin initial facts
      Cache.empty_valid universeNodeAvailable markerNodeAvailable leaves
  have actualForward : SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 7
      (second entry bodyEntry bodyRows depth ordinary initial).1
      marker (.reference (.interned entry.identity)) entered = .done forward forwardFinal := by
    rw [markerEq]
    exact forwardDone
  have actualBackward : SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 8
      (second entry bodyEntry bodyRows depth ordinary initial).1
      (.reference (.interned entry.identity)) marker entered = .done backward backwardFinal := by
    rw [markerEq]
    exact backwardDone
  exact ⟨entry, body, depth, ordinary, heap, bodyEntry, bodyRows, marker, forward, forwardFinal,
    backward, backwardFinal, built, facts, universeAvailable, shape, bodyEq, closed, markerRead, member,
    initialValid, enteredValid, universeAvailable, markerAvailable, referenceAvailable,
    actualForward, forwardFacts, forwardAvailable, forwardClosed,
    actualBackward, backwardFacts, backwardAvailable, backwardClosed⟩

end MicroCFTA.SourceSynthesisUniverseMarkerCrossInput
