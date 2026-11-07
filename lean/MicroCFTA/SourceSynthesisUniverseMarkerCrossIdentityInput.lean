import MicroCFTA.SourceSynthesisUniverseMarkerIdentityInput
import MicroCFTA.SourceSynthesisUniverseMarkerReferenceIdentity
import MicroCFTA.SourceSynthesisUniverseSecondDomain

/-!
# Original synthesis inputs classify both marker/reference cross-children

Original construction supplies the actual universe, body, and marker.
The two actual domain allocations derive the complete second-domain
invariant and the extension from the initial machine. Both cross-child
requests start in this same second machine. Each result is EmptyNode or
the original marker. Catalog membership and the full body product remain
separate obligations.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerCrossIdentityInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniverseBodyReferenceControl (second secondState)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original inputs derive both classified runs and the actual entered domain with its cache history. -/
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
      SourceRecursiveIntersectionKernel.Extension initial entered ∧
      SourceRecursiveIntersectionKernel.Domain entered (second entry bodyEntry bodyRows depth ordinary initial).1 ∧
      Available entered.heap (.mu entry body depth ordinary) ∧ Available entered.heap marker ∧
      Available entered.heap (.reference (.interned entry.identity)) ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 7
        (second entry bodyEntry bodyRows depth ordinary initial).1
        marker (.reference (.interned entry.identity)) entered = .done forward forwardFinal ∧
      Facts forwardFinal.heap ∧ Available forwardFinal.heap forward ∧ forward.free = [] ∧
      (forward = .empty ∨ forward = marker) ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 8
        (second entry bodyEntry bodyRows depth ordinary initial).1
        (.reference (.interned entry.identity)) marker entered = .done backward backwardFinal ∧
      Facts backwardFinal.heap ∧ Available backwardFinal.heap backward ∧ backward.free = [] ∧
      (backward = .empty ∨ backward = marker) := by
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
  obtain ⟨enteredValid, enteredExtension, enteredDomain⟩ :=
    SourceSynthesisUniverseSecondDomain.second_checked entry bodyEntry bodyRows depth ordinary initial
      facts Cache.empty_valid universeNodeAvailable
  have markerTop : markerEdge.entry.key.constraint = top :=
    SourceSynthesisUniverseMarkerIdentityInput.marker_row_guard "(->)" top markerEntry markerEdge marker
      markerRead markerEq
  have bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top :=
    SourceSynthesisUniverseBodyRowKinds.node_guards top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity)
      bodyEntry bodyRows 0 [.interned entry.identity] (by rw [← bodyEq]; exact shape)
  obtain ⟨forward, forwardFinal, forwardDone, forwardFacts, forwardAvailable, forwardNode⟩ :=
    SourceSynthesisUniverseMarkerReferenceIdentity.marker_reference_complete entry bodyEntry markerEntry
      bodyRows markerEdge depth ordinary top SourceEqualityPCSNativeEdge.conjoin top
      SourceSynthesisUniverseTopConjunction.native_conjoin_top initial facts Cache.empty_valid
      universeNodeAvailable markerNodeAvailable markerChildren markerTop bodyTop
  obtain ⟨backward, backwardFinal, backwardDone, backwardFacts, backwardAvailable, backwardNode⟩ :=
    SourceSynthesisUniverseMarkerReferenceIdentity.reference_marker_complete entry bodyEntry markerEntry
      bodyRows markerEdge depth ordinary top SourceEqualityPCSNativeEdge.conjoin top
      SourceSynthesisUniverseTopConjunction.native_conjoin_top initial facts Cache.empty_valid
      universeNodeAvailable markerNodeAvailable markerChildren markerTop bodyTop
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
  have forwardClass : forward = .empty ∨ forward = marker := by
    rcases forwardNode with emptyCase | markerCase
    · exact Or.inl emptyCase
    · exact Or.inr (markerCase.trans markerEq.symm)
  have backwardClass : backward = .empty ∨ backward = marker := by
    rcases backwardNode with emptyCase | markerCase
    · exact Or.inl emptyCase
    · exact Or.inr (markerCase.trans markerEq.symm)
  have resultClosed : ∀ value : Value String Guard, (value = .empty ∨ value = marker) → value.free = [] := by
    intro value classified
    rcases classified with emptyCase | markerCase
    · rw [emptyCase]
      rfl
    · rw [markerCase, markerEq]
      rfl
  exact ⟨entry, body, depth, ordinary, heap, bodyEntry, bodyRows, marker, forward, forwardFinal,
    backward, backwardFinal, built, facts, universeAvailable, shape, bodyEq, closed, markerRead, member,
    initialValid, enteredValid, enteredExtension, enteredDomain, universeAvailable, markerAvailable,
    referenceAvailable, actualForward, forwardFacts, forwardAvailable, resultClosed forward forwardClass,
    forwardClass, actualBackward, backwardFacts, backwardAvailable, resultClosed backward backwardClass, backwardClass⟩

end MicroCFTA.SourceSynthesisUniverseMarkerCrossIdentityInput
