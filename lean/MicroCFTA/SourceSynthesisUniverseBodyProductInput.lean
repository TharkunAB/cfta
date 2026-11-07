import MicroCFTA.SourceSynthesisUniverseMarkerIdentityInput
import MicroCFTA.SourceSynthesisUniverseSecondDomain
import MicroCFTA.SourceSynthesisUniverseBodyProductCompletion

/-!
# Original synthesis inputs complete the actual universe-body product

Original construction supplies the universe and its retained marker.
Actual row readback derives every guard and child case. The complete source
row walk then constructs the body product in the real second machine.
The nine-level B/B request has this same result and final caches. Its free
list is empty or the single diagonal intersection reference. The returned
value prepares without an open Mu. Outer Mu reconstruction is separate.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyProductInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open SourceRecursiveIntersectionControl (pair)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original inputs derive the full actual body product and its direct B/B execution. -/
theorem typesOf_body_complete (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap bodyEntry bodyRows marker value final,
      let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
      let entered := secondState entry bodyEntry bodyRows depth ordinary initial
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      SourceSynthesisUniverseBody.RowReadback "(->)" top [] marker ∧
      marker ∈ children body ∧ Available heap marker ∧
      SourceRecursiveIntersectionKernel.Valid initial ∧ SourceRecursiveIntersectionKernel.Valid entered ∧
      SourceRecursiveIntersectionKernel.Extension initial entered ∧
      SourceRecursiveIntersectionKernel.Domain entered (second entry bodyEntry bodyRows depth ordinary initial).1 ∧
      SourceRecursiveIntersectionKernel.node top SourceEqualityPCSNativeEdge.conjoin
        (SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 8
          (second entry bodyEntry bodyRows depth ordinary initial).1)
        bodyRows bodyRows entered = .done value final ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 9
        (second entry bodyEntry bodyRows depth ordinary initial).1 body body entered = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      SourceRecursiveIntersectionKernel.Extension entered final ∧ Available final.heap value ∧
      PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free =
        [.intersection (pair entry.identity entry.identity).1 (pair entry.identity entry.identity).2]) := by
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
  let entered := secondState entry bodyEntry bodyRows depth ordinary initial
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, Cache.empty_valid⟩
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
  obtain ⟨value, final, nodeDone, finalValid, growth, available, prepared, freeShape⟩ :=
    SourceSynthesisUniverseBodyProductCompletion.node_complete entry bodyEntry markerEntry bodyRows markerEdge
      depth ordinary top SourceEqualityPCSNativeEdge.conjoin top
      SourceSynthesisUniverseTopConjunction.native_conjoin_top initial facts Cache.empty_valid
      universeNodeAvailable markerNodeAvailable markerChildren markerTop bodyTop bodyChildren
  have actualDone : SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 9
      (second entry bodyEntry bodyRows depth ordinary initial).1 body body entered = .done value final := by
    rw [bodyEq]
    change SourceRecursiveIntersectionKernel.onNode top SourceEqualityPCSNativeEdge.conjoin
      (SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 8)
      (second entry bodyEntry bodyRows depth ordinary initial).1
      (.node bodyEntry bodyRows 0 [.interned entry.identity])
      (.node bodyEntry bodyRows 0 [.interned entry.identity]) entered = .done value final
    rw [SourceSynthesisUniverseBodyReferenceControl.body_diagonal_onNode entry bodyEntry bodyRows depth ordinary
      top SourceEqualityPCSNativeEdge.conjoin _ initial facts Cache.empty_valid universeNodeAvailable]
    exact nodeDone
  exact ⟨entry, body, depth, ordinary, heap, bodyEntry, bodyRows, marker, value, final, built, facts,
    universeAvailable, shape, bodyEq, closed, markerRead, member, markerAvailable, initialValid,
    enteredValid, enteredExtension, enteredDomain, nodeDone, actualDone, finalValid, growth, available, prepared, freeShape⟩

end MicroCFTA.SourceSynthesisUniverseBodyProductInput
