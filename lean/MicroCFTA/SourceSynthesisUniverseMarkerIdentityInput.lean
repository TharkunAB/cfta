import MicroCFTA.SourceSynthesisUniverseMarkerInput
import MicroCFTA.SourceSynthesisUniverseBodyRowKinds
import MicroCFTA.SourceSynthesisUniverseMarkerIdentity
import MicroCFTA.SourceSynthesisUniverseTopConjunction

/-!
# Original synthesis inputs derive marker identity or EmptyNode

The original Library and Query data construct the actual type universe.
Body row classification derives every retained top guard. Literal marker
readback derives its own top guard. The actual five-level source request
then returns either EmptyNode or that original marker. Catalog membership
does not yet decide which result occurs.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerIdentityInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax

section Generic
variable {Guard : Type}

/-- Literal marker readback identifies the guard of its actual stored row. -/
theorem marker_row_guard (label : String) (top : Guard) (entry : Interned NodeKey)
    (row : EdgeValue String Guard) (marker : Value String Guard)
    (readback : SourceSynthesisUniverseBody.RowReadback label top [] marker)
    (node : marker = .node entry [row] 0 []) : row.entry.key.constraint = top := by
  obtain ⟨_, actualRow, same, _, key⟩ := readback
  have rowsEq := (Value.node.inj (node.symm.trans same)).2.1
  have rowEq : row = actualRow := (List.cons.inj rowsEq).1
  rw [rowEq]
  exact congrArg EdgeKey.constraint key

end Generic

open SourceSynthesisGeneralizeSyntax (Guard top)
variable [DecidableEq (EdgeKey String Guard)]

/-- Original inputs derive the actual completed request and its marker-or-empty classification. -/
theorem typesOf_marker_complete (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap marker value final,
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      SourceSynthesisUniverseBody.RowReadback "(->)" top [] marker ∧
      marker ∈ children body ∧ Available heap marker ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 5
        IntersectionEmptyDomain.emptyDomain marker (.mu entry body depth ordinary)
        ⟨heap, Cache.emptyState⟩ = .done value final ∧
      Facts final.heap ∧ Available final.heap value ∧ value.free = [] ∧
      (value = .empty ∨ value = marker) := by
  obtain ⟨entry, body, depth, ordinary, heap, built, facts, universeAvailable, shape, closed⟩ :=
    SourceSynthesisUniverseColdReadback.typesOf_cold_mu lib query
  obtain ⟨bodyEntry, bodyRows, markerEntry, markerEdge, marker, bodyEq, markerEq,
      markerRead, markerChildren, member, markerAvailable⟩ :=
    SourceSynthesisUniverseMarkerInput.shape_marker_available top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
      entry body depth ordinary heap universeAvailable shape
  let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, Cache.empty_valid⟩
  have markerNodeAvailable : Available initial.heap (.node markerEntry [markerEdge] 0 []) := by
    rw [← markerEq]
    exact markerAvailable
  have universeNodeAvailable : Available initial.heap
      (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    rw [← bodyEq]
    exact universeAvailable
  have markerTop : markerEdge.entry.key.constraint = top :=
    marker_row_guard "(->)" top markerEntry markerEdge marker markerRead markerEq
  have bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top :=
    SourceSynthesisUniverseBodyRowKinds.node_guards top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity)
      bodyEntry bodyRows 0 [.interned entry.identity] (by rw [← bodyEq]; exact shape)
  obtain ⟨value, final, done, finalFacts, available, classifiedNode⟩ :=
    SourceSynthesisUniverseMarkerIdentity.marker_universe_complete top SourceEqualityPCSNativeEdge.conjoin top
      SourceSynthesisUniverseTopConjunction.native_conjoin_top markerEntry bodyEntry entry markerEdge bodyRows
      depth ordinary initial initialValid markerNodeAvailable universeNodeAvailable markerChildren markerTop bodyTop
  have actualDone : SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 5
      IntersectionEmptyDomain.emptyDomain marker (.mu entry body depth ordinary) initial = .done value final := by
    rw [markerEq, bodyEq]
    exact done
  have classified : value = .empty ∨ value = marker := by
    rcases classifiedNode with emptyCase | markerCase
    · exact Or.inl emptyCase
    · exact Or.inr (markerCase.trans markerEq.symm)
  have resultClosed : value.free = [] := by
    rcases classified with emptyCase | markerCase
    · rw [emptyCase]
      rfl
    · rw [markerCase, markerEq]
      rfl
  exact ⟨entry, body, depth, ordinary, heap, marker, value, final, built, facts, universeAvailable,
    shape, closed, markerRead, member, markerAvailable, actualDone, finalFacts, available, resultClosed, classified⟩

end MicroCFTA.SourceSynthesisUniverseMarkerIdentityInput
