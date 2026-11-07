import MicroCFTA.SourceSynthesisUniverseBody

/-!
# Source rows retained in the actual type-universe body

Canonical edge ordering selects complete original rows. Each retained row
is the distinguished arrow or a row from the rigid and catalog descriptors.
All guards equal the supplied top guard. Each child is the actual marker
or the local reference. Catalog entries can repeat and can use arrow names.
The statements do not require residency of discarded source rows.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyRowKinds
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisUniverseBody (Shape RowReadback RowKeys descriptors)

variable {Guard : Type}

private theorem output_origin {A B : Type} {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (aligned : All₂ R inputs outputs) : ∀ value ∈ outputs, ∃ input ∈ inputs, R input value := by
  induction aligned with
  | nil => intro value member; cases member
  | @cons first value rest values own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self, own⟩
      · obtain ⟨input, present, related⟩ := ih selected later
        exact ⟨input, List.mem_cons_of_mem _ present, related⟩

/-- Each retained actual row has its arrow or descriptor source readback. -/
theorem row_kinds (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (value : Value String Guard) (shape : Shape top catalog name value) :
    ∃ entry rows marker,
      value = .node entry rows 0 [name] ∧ RowReadback "(->)" top [] marker ∧
      ∀ row ∈ rows,
        (row.children = [marker, .reference name, .reference name] ∧
          row.entry.key = ⟨"->", [marker.referenceOf, .ref name, .ref name], top⟩) ∨
        ∃ descriptor ∈ descriptors catalog, RowKeys top name descriptor row := by
  obtain ⟨entry, marker, arrow, rest, same, markerRead, arrowChildren, arrowKey, aligned⟩ := shape
  refine ⟨entry, _, marker, same, markerRead, ?_⟩
  intro row retained
  have original := (List.mem_filter.mp (canonicalEdges_member _ row retained)).1
  rcases List.mem_cons.mp original with rfl | later
  · exact Or.inl ⟨arrowChildren, arrowKey⟩
  · exact Or.inr (output_origin aligned row later)

/-- The same actual node and marker also give every retained guard and child. -/
theorem readback (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (value : Value String Guard) (shape : Shape top catalog name value) :
    ∃ entry rows marker,
      value = .node entry rows 0 [name] ∧ RowReadback "(->)" top [] marker ∧
      (∀ row ∈ rows,
        (row.children = [marker, .reference name, .reference name] ∧
          row.entry.key = ⟨"->", [marker.referenceOf, .ref name, .ref name], top⟩) ∨
        ∃ descriptor ∈ descriptors catalog, RowKeys top name descriptor row) ∧
      (∀ row ∈ rows, row.entry.key.constraint = top) ∧
      (∀ row ∈ rows, ∀ child ∈ row.children, child = marker ∨ child = .reference name) := by
  obtain ⟨entry, rows, marker, same, markerRead, kinds⟩ := row_kinds top catalog name value shape
  refine ⟨entry, rows, marker, same, markerRead, kinds, ?_, ?_⟩
  · intro row retained
    rcases kinds row retained with arrow | ⟨descriptor, _, related⟩
    · exact congrArg EdgeKey.constraint arrow.2
    · exact congrArg EdgeKey.constraint related.2
  · intro row retained child selected
    rcases kinds row retained with arrow | ⟨descriptor, _, related⟩
    · rw [arrow.1] at selected
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using selected
    · rw [related.1] at selected
      exact Or.inr (List.eq_of_mem_replicate selected)

/-- Shape on an existing node directly supplies the guard premise for all of its rows. -/
theorem node_guards (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (entry : Interned NodeKey) (rows : List (EdgeValue String Guard)) (depth : Nat) (free : List Reference)
    (shape : Shape top catalog name (.node entry rows depth free)) :
    ∀ row ∈ rows, row.entry.key.constraint = top := by
  obtain ⟨_, actualRows, _, same, _, _, guards, _⟩ :=
    readback top catalog name (.node entry rows depth free) shape
  have rowsEq : rows = actualRows := (Value.node.inj same).2.1
  rw [rowsEq]
  exact guards

end MicroCFTA.SourceSynthesisUniverseBodyRowKinds
