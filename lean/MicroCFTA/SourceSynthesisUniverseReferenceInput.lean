import MicroCFTA.SourceSynthesisUniverseReferenceCompletion
import MicroCFTA.SourceSynthesisUniverseMarkerIdentityInput

/-!
# Original synthesis inputs complete the open universe request

Original Library and Query data construct the source universe from empty
caches. Its actual retained rows supply every guard and child case.
The thirteen-level open-reference/universe request completes with a closed
available output. Both actual cache histories extend the initial machine.
The returned value is not classified as the original universe here.
-/
namespace MicroCFTA.SourceSynthesisUniverseReferenceInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedRecordCoherence (Covered)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original inputs derive actual request completion, closed output, and both cache invariants. -/
theorem typesOf_reference_complete (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap value final,
      let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      SourceRecursiveIntersectionKernel.Valid initial ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 13
        IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity))
        (.mu entry body depth ordinary) initial = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ SourceRecursiveIntersectionKernel.Extension initial final ∧
      Available final.heap value ∧ Covered [] final.heap ∧ value.free = [] := by
  obtain ⟨entry, body, depth, ordinary, heap, built, facts, universeAvailable, shape, closed⟩ :=
    SourceSynthesisUniverseColdReadback.typesOf_cold_mu lib query
  obtain ⟨bodyEntry, bodyRows, markerEntry, markerEdge, marker, bodyEq, markerEq,
      markerRead, markerChildren, member, markerAvailable⟩ :=
    SourceSynthesisUniverseMarkerInput.shape_marker_available top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
      entry body depth ordinary heap universeAvailable shape
  obtain ⟨_, readRows, readMarker, readNode, _, _, rowGuards, childKinds⟩ :=
    SourceSynthesisUniverseBodyRowKinds.readback top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity) body shape
  have rowsEq : bodyRows = readRows := (Value.node.inj (bodyEq.symm.trans readNode)).2.1
  have readMember : marker ∈ readRows.flatMap EdgeValue.children := by
    have occurrence := member
    rw [readNode] at occurrence
    exact occurrence
  obtain ⟨sourceRow, sourceMember, childMember⟩ := List.mem_flatMap.mp readMember
  have markerSame : marker = readMarker := by
    rcases childKinds sourceRow sourceMember marker childMember with same | referenceCase
    · exact same
    · rw [markerEq] at referenceCase
      cases referenceCase
  have bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top := by
    rw [rowsEq]
    exact rowGuards
  have bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node markerEntry [markerEdge] 0 [] ∨ child = .reference (.interned entry.identity) := by
    rw [rowsEq]
    simpa only [← markerSame, markerEq] using childKinds
  let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, Cache.empty_valid⟩
  have markerNodeAvailable : Available initial.heap (.node markerEntry [markerEdge] 0 []) := by
    rw [← markerEq]
    exact markerAvailable
  have markerTop : markerEdge.entry.key.constraint = top :=
    SourceSynthesisUniverseMarkerIdentityInput.marker_row_guard "(->)" top markerEntry markerEdge marker
      markerRead markerEq
  have nodeBuilt :
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query) [] empty =
        .done (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary) initial.heap := by
    rw [← bodyEq]
    exact built
  obtain ⟨value, final, done, finalValid, growth, available, covered, resultClosed⟩ :=
    SourceSynthesisUniverseReferenceCompletion.execute_reference_complete_of_built
      entry bodyEntry markerEntry bodyRows markerEdge depth ordinary top SourceEqualityPCSNativeEdge.conjoin top
      SourceSynthesisUniverseTopConjunction.native_conjoin_top initial Cache.empty_valid markerNodeAvailable
      markerChildren markerTop bodyTop bodyChildren (SourceSynthesisFirstOrderConstruction.typesOf lib query) nodeBuilt
  have actualDone : SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 13
      IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity))
      (.mu entry body depth ordinary) initial = .done value final := by
    rw [bodyEq]
    exact done
  exact ⟨entry, body, depth, ordinary, heap, value, final, built, facts, universeAvailable, shape, closed,
    initialValid, actualDone, finalValid, growth, available, covered, resultClosed⟩

end MicroCFTA.SourceSynthesisUniverseReferenceInput
