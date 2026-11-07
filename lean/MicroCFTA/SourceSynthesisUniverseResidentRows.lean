import MicroCFTA.SourceSynthesisUniverseBody

/-!
# Resident raw rows of the actual universe callback

The packet retains the complete raw arrow and catalog rows.
It records their actual edge-cache residency before canonical ordering.
Record growth preserves the same witnesses. Current cache facts derive
the marker availability, guards, child shapes, and live-row properties.
-/
namespace MicroCFTA.SourceSynthesisUniverseResidentRows
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference)
open SourceSynthesisTypeSyntax (allTypesBody)
open SourceSynthesisUniverseBody (RowReadback RowKeys descriptors)

variable {Guard : Type}

/-- The actual callback retains these exact raw witnesses and their complete resident records. -/
def Rows (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (value : Value String Guard) (heap : InternedConstructorTemplates.State String Guard) : Prop :=
  ∃ entry marker arrow catalogRows,
    value = .node entry (canonicalEdges (arrow :: catalogRows)) 0 [name] ∧
    RowReadback "(->)" top [] marker ∧
    arrow.children = [marker, .reference name, .reference name] ∧
    arrow.entry.key = ⟨"->", [marker.referenceOf, .ref name, .ref name], top⟩ ∧
    All₂ (RowKeys top name) (descriptors catalog) catalogRows ∧
    ∀ row ∈ arrow :: catalogRows, EdgeResident heap row

/-- Actual record growth preserves every raw witness without an issued-name assumption. -/
theorem Rows.grows {top : Guard} {catalog : List (String × Nat)} {name : Reference}
    {value : Value String Guard} {before after : InternedConstructorTemplates.State String Guard}
    (rows : Rows top catalog name value before) (growth : Grows before after) :
    Rows top catalog name value after := by
  obtain ⟨entry, marker, arrow, rest, same, markerRead, arrowChildren, arrowKey, aligned, resident⟩ := rows
  exact ⟨entry, marker, arrow, rest, same, markerRead, arrowChildren, arrowKey, aligned,
    fun row member => edge_grows before after growth row (resident row member)⟩

/-- The repaired source callback derives its raw-row packet from the actual initial inputs. -/
theorem callback_rows [DecidableEq (EdgeKey String Guard)]
    (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (state : InternedConstructorTemplates.State String Guard) (facts : Facts state)
    (available : Available state (.reference name)) :
    ∃ value final,
      callback (allTypesBody top catalog) [] name state = .done value final ∧
      Facts final ∧ Available final value ∧ Rows top catalog name value final := by
  obtain ⟨value, final, done, _, finalFacts, finalAvailable, rows⟩ :=
    SourceSynthesisUniverseBody.callback_readback_with_rows top catalog name state facts available
  exact ⟨value, final, done, finalFacts, finalAvailable, rows⟩

private theorem catalog_fields (top : Guard) (name : Reference) (marker : Value String Guard)
    (inputs : List (String × Nat)) (rows : List (EdgeValue String Guard))
    (aligned : All₂ (RowKeys top name) inputs rows) :
    ∀ row ∈ rows, row.entry.key.constraint = top ∧
      ∀ child ∈ row.children, child = marker ∨ child = .reference name := by
  induction aligned with
  | nil => intro row member; cases member
  | @cons descriptor row inputs rows own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with same | later
      · subst selected
        refine ⟨congrArg EdgeKey.constraint own.2, ?_⟩
        intro child present
        rw [own.1] at present
        exact Or.inr (List.eq_of_mem_replicate present)
      · exact ih selected later

/-- One consistent raw witness also supplies its marker, row properties, and retained arrow. -/
theorem Rows.readback {top : Guard} {catalog : List (String × Nat)} {name : Reference}
    {value : Value String Guard} {heap : InternedConstructorTemplates.State String Guard}
    (rows : Rows top catalog name value heap) (facts : Facts heap) :
    ∃ entry marker arrow catalogRows,
      value = .node entry (canonicalEdges (arrow :: catalogRows)) 0 [name] ∧
      RowReadback "(->)" top [] marker ∧
      arrow.children = [marker, .reference name, .reference name] ∧
      arrow.entry.key = ⟨"->", [marker.referenceOf, .ref name, .ref name], top⟩ ∧
      All₂ (RowKeys top name) (descriptors catalog) catalogRows ∧
      (∀ row ∈ arrow :: catalogRows, EdgeResident heap row) ∧
      marker.free = [] ∧ Available heap marker ∧
      (∀ row ∈ arrow :: catalogRows, row.entry.key.constraint = top) ∧
      (∀ row ∈ arrow :: catalogRows, ∀ child ∈ row.children,
        child = marker ∨ child = .reference name) ∧
      (∀ row ∈ arrow :: catalogRows, EqualityLeafProjectionPhysical.dead row = false) ∧
      arrow ∈ canonicalEdges (arrow :: catalogRows) ∧ canonicalEdges (arrow :: catalogRows) ≠ [] := by
  obtain ⟨entry, marker, arrow, rest, same, markerRead, arrowChildren, arrowKey, aligned, resident⟩ := rows
  have markerFields : marker.free = [] ∧ marker.referenceOf ≠ .empty := by
    obtain ⟨markerEntry, markerRow, markerEq, _, _⟩ := markerRead
    constructor
    · simp [markerEq, Value.free, childFree, canonicalFree]
    · simp [markerEq, Value.referenceOf]
  have markerAvailable : Available heap marker :=
    facts.cached.edges arrow.entry.key arrow (resident arrow List.mem_cons_self) marker
      (by rw [arrowChildren]; exact List.mem_cons_self)
  have catalogFields := catalog_fields top name marker (descriptors catalog) rest aligned
  have guards : ∀ row ∈ arrow :: rest, row.entry.key.constraint = top := by
    intro row member
    rcases List.mem_cons.mp member with same | later
    · subst row
      exact congrArg EdgeKey.constraint arrowKey
    · exact (catalogFields row later).1
  have kinds : ∀ row ∈ arrow :: rest, ∀ child ∈ row.children,
      child = marker ∨ child = .reference name := by
    intro row member child selected
    rcases List.mem_cons.mp member with same | later
    · subst row
      rw [arrowChildren] at selected
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using selected
    · exact (catalogFields row later).2 child selected
  have live : ∀ row ∈ arrow :: rest, EqualityLeafProjectionPhysical.dead row = false := by
    intro row member
    apply List.any_eq_false.mpr
    intro child selected
    rcases kinds row member child selected with same | same
    · rw [same]
      intro equal
      exact markerFields.2 (beq_iff_eq.mp equal)
    · simp [same, Value.referenceOf]
  have retained : arrow ∈ canonicalEdges (arrow :: rest) :=
    canonicalEdges_retains heap facts.coherent (arrow :: rest) arrow resident List.mem_cons_self
  have nonempty : canonicalEdges (arrow :: rest) ≠ [] := by
    intro absent
    simp only [absent, List.not_mem_nil] at retained
  exact ⟨entry, marker, arrow, rest, same, markerRead, arrowChildren, arrowKey, aligned, resident,
    markerFields.1, markerAvailable, guards, kinds, live, retained, nonempty⟩

end MicroCFTA.SourceSynthesisUniverseResidentRows
