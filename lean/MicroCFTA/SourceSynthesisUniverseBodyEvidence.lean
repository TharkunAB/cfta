import MicroCFTA.SourceSynthesisUniverseMarkerIdentityInput

/-!
# Consistent actual marker and arrow witnesses for universe normalization

The same retained marker supplies its complete literal readback, available
record, and the distinguished arrow child. Every retained row uses this
marker or the local reference. Marker provenance aligns the existential
readback witnesses. Catalog rows contain only references, so a row with
the marker child must have the distinguished arrow shape.
No discarded-row residency, catalog uniqueness, or heap facts are assumed.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyEvidence
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceSynthesisUniverseBody (Shape RowReadback RowKeys descriptors)

variable {Guard : Type}

/-- Actual Mu availability and body shape derive one consistent complete row witness packet. -/
theorem of_shape (top : Guard) (catalog : List (String × Nat)) (u b : Interned NodeKey)
    (bodyRows : List (EdgeValue String Guard)) (depth ordinary : Value String Guard)
    (heap : InternedConstructorTemplates.State String Guard)
    (available : Available heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (shape : Shape top catalog (.interned u.identity) (.node b bodyRows 0 [.interned u.identity])) :
    ∃ m markerRow arrow,
      let marker : Value String Guard := .node m [markerRow] 0 []
      RowReadback "(->)" top [] marker ∧ markerRow.children = [] ∧
      markerRow.entry.key.constraint = top ∧ Available heap marker ∧
      arrow ∈ bodyRows ∧ arrow.children = [marker, .reference (.interned u.identity), .reference (.interned u.identity)] ∧
      arrow.entry.key = ⟨"->", [marker.referenceOf, .ref (.interned u.identity), .ref (.interned u.identity)], top⟩ ∧
      (∀ row ∈ bodyRows,
        (row.children = [marker, .reference (.interned u.identity), .reference (.interned u.identity)] ∧
          row.entry.key = ⟨"->", [marker.referenceOf, .ref (.interned u.identity), .ref (.interned u.identity)], top⟩) ∨
        ∃ descriptor ∈ descriptors catalog, RowKeys top (.interned u.identity) descriptor row) ∧
      (∀ row ∈ bodyRows, row.entry.key.constraint = top) ∧
      (∀ row ∈ bodyRows, ∀ child ∈ row.children, child = marker ∨ child = .reference (.interned u.identity)) := by
  obtain ⟨_, _, m, markerRow, originalMarker, _, markerEq, markerRead, leaf, member, markerAvailable⟩ :=
    SourceSynthesisUniverseMarkerInput.shape_marker_available top catalog u
      (.node b bodyRows 0 [.interned u.identity]) depth ordinary heap available shape
  obtain ⟨_, readRows, readMarker, readNode, _, rowKinds, rowGuards, childKinds⟩ :=
    SourceSynthesisUniverseBodyRowKinds.readback top catalog (.interned u.identity)
      (.node b bodyRows 0 [.interned u.identity]) shape
  have rowsEq : bodyRows = readRows := (Value.node.inj readNode).2.1
  have occurrence : originalMarker ∈ readRows.flatMap EdgeValue.children := by
    rw [← rowsEq]
    exact member
  obtain ⟨arrow, arrowMember, childMember⟩ := List.mem_flatMap.mp occurrence
  have markerSame : originalMarker = readMarker := by
    rcases childKinds arrow arrowMember originalMarker childMember with same | referenceCase
    · exact same
    · rw [markerEq] at referenceCase
      cases referenceCase
  let marker : Value String Guard := .node m [markerRow] 0 []
  have actualKinds : ∀ row ∈ bodyRows,
      (row.children = [marker, .reference (.interned u.identity), .reference (.interned u.identity)] ∧
        row.entry.key = ⟨"->", [marker.referenceOf, .ref (.interned u.identity), .ref (.interned u.identity)], top⟩) ∨
      ∃ descriptor ∈ descriptors catalog, RowKeys top (.interned u.identity) descriptor row := by
    rw [rowsEq]
    simpa only [← markerSame, markerEq] using rowKinds
  have actualGuards : ∀ row ∈ bodyRows, row.entry.key.constraint = top := by
    rw [rowsEq]
    exact rowGuards
  have actualChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = marker ∨ child = .reference (.interned u.identity) := by
    rw [rowsEq]
    simpa only [← markerSame, markerEq] using childKinds
  have retained : arrow ∈ bodyRows := by rw [rowsEq]; exact arrowMember
  have arrowShape : arrow.children = [marker, .reference (.interned u.identity), .reference (.interned u.identity)] ∧
      arrow.entry.key = ⟨"->", [marker.referenceOf, .ref (.interned u.identity), .ref (.interned u.identity)], top⟩ := by
    rcases actualKinds arrow retained with own | ⟨descriptor, _, related⟩
    · exact own
    · rw [related.1] at childMember
      have impossible := List.eq_of_mem_replicate childMember
      rw [markerEq] at impossible
      cases impossible
  have actualRead : RowReadback "(->)" top [] marker := by
    change RowReadback "(->)" top [] (.node m [markerRow] 0 [])
    rw [← markerEq]
    exact markerRead
  have actualAvailable : Available heap marker := by
    change Available heap (.node m [markerRow] 0 [])
    rw [← markerEq]
    exact markerAvailable
  have markerTop : markerRow.entry.key.constraint = top :=
    SourceSynthesisUniverseMarkerIdentityInput.marker_row_guard "(->)" top m markerRow originalMarker markerRead markerEq
  exact ⟨m, markerRow, arrow, actualRead, leaf, markerTop, actualAvailable, retained,
    arrowShape.1, arrowShape.2, actualKinds, actualGuards, actualChildren⟩

end MicroCFTA.SourceSynthesisUniverseBodyEvidence
