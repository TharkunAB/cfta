import MicroCFTA.SourceRecursiveIntersectionInputView

/-!
# Free names of copied original physical syntax

Copying retains exact interned free-name membership. Coherent original
records supply the cached equations. No copy-closed contract is assumed.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule

/-- Copied physical member lists retain exactly their children's free names. -/
theorem shapeValues_free (holds : Guard → Language.Term Symbol → Bool) (values : List (Value Symbol Guard)) (name : Nat) :
    name ∈ Binding.freeList (shapeValues holds values) ↔ ∃ value ∈ values, name ∈ Binding.free (shape holds value) := by
  induction values with
  | nil => simp [shapeValues, Binding.freeList]
  | cons first rest ih => simp [shapeValues, Binding.freeList, ih]

/-- Copied rows retain exactly the free names of their ordered child records. -/
theorem shapeEdges_free (holds : Guard → Language.Term Symbol → Bool) (edges : List (EdgeValue Symbol Guard)) (name : Nat) :
    name ∈ Binding.freeList (shapeEdges holds edges) ↔
      ∃ edge ∈ edges, ∃ child ∈ edge.children, name ∈ Binding.free (shape holds child) := by
  induction edges with
  | nil => simp [shapeEdges, Binding.freeList]
  | cons first rest ih => simp [shapeEdges, Binding.freeList, shapeEdge, Binding.free, shapeValues_free, ih]

/-- Copied original syntax has exactly the interned free names of the actual cached field. -/
theorem shape_free (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (available : Available state value)
    (name : Nat) : name ∈ Binding.free (shape holds value) ↔ name ∈ freeNames value := by
  induction available with
  | intro value resident issued children ih =>
      cases value with
      | empty => simp [shape, Binding.free, freeNames, Value.free]
      | reference reference =>
          cases reference <;> simp [shape, Binding.free, freeNames, Value.free, internedName]
      | node entry edges depth free =>
          rw [freeNames_member]
          simp only [shape, Binding.free, shapeEdges_free, Value.free,
            InternedNormalizationFree.node_free state facts.coherent entry edges depth free resident, childFree_member]
          constructor
          · rintro ⟨edge, present, child, inside, named⟩
            have inChildren := List.mem_flatMap.mpr ⟨edge, present, inside⟩
            exact ⟨child, inChildren, (freeNames_member child name).mp ((ih child inChildren).mp named)⟩
          · rintro ⟨child, inChildren, named⟩
            obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp inChildren
            exact ⟨edge, present, child, inside, (ih child inChildren).mpr ((freeNames_member child name).mpr named)⟩
      | union entry members depth free =>
          rw [freeNames_member]
          simp only [shape, Binding.free, shapeValues_free, Value.free,
            InternedNormalizationFree.union_free state facts.coherent entry members depth free resident, childFree_member]
          constructor
          · rintro ⟨child, present, named⟩
            exact ⟨child, present, (freeNames_member child name).mp ((ih child present).mp named)⟩
          · rintro ⟨child, present, named⟩
            exact ⟨child, present, (ih child present).mpr ((freeNames_member child name).mpr named)⟩
      | mu entry body depth ordinary =>
          simp only [shape, Binding.free, List.mem_filter, bne_iff_ne]
          rw [freeNames_member]
          simp only [Value.free, List.mem_filter, bne_iff_ne]
          rw [ih body (by simp [InternedProbeProvenance.children]), freeNames_member]
          simp

/-- Copied payload readback retains exact cached interned free-name membership. -/
theorem copy_free (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (available : Available state value)
    (input : Input) (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) (name : Nat) :
    name ∈ Binding.free ((view state holds).copy input) ↔ name ∈ (view state holds).free input := by
  rw [copy_readback state facts holds value available input complete]
  have inputExact := inputOf_codec value input complete
  rw [← inputExact, free_readback state facts holds value available]
  exact shape_free state facts holds value available name

/-- Every input of the total physical view has exact copied free-name membership. -/
theorem copy_free_all (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (input : Input) (name : Nat) :
    name ∈ Binding.free ((view state holds).copy input) ↔ name ∈ (view state holds).free input := by
  have selectedFree (input : Input) (identity : Nat)
      (tagged : input = .node identity ∨ input = .mu identity ∨ input = .union identity) :
      name ∈ Binding.free ((view state holds).copy input) ↔ name ∈ (view state holds).free input := by
    rcases payload_selected state identity input tagged with absent | ⟨value, found, same, selected⟩
    · simp only [view, absent, shape, Binding.free, freeNames, Value.free, List.filterMap_nil]
    · simpa only [view, selected] using
        shape_free state facts holds value (SourcePreparedSharedRows.read_available state facts identity value found) name
  cases input with
  | empty => simp [view, payload, shape, Binding.free, freeNames, Value.free]
  | ref reference => simp [view, payload, shape, Binding.free, freeNames, Value.free, internedName]
  | node identity => exact selectedFree _ identity (.inl rfl)
  | mu identity => exact selectedFree _ identity (.inr (.inl rfl))
  | union identity => exact selectedFree _ identity (.inr (.inr rfl))

/-- Actual physical copies of closed inputs are closed, without a supplied copy contract. -/
theorem copy_closed (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) : CopyClosed (view state holds) := by
  intro input isClosed
  have empty : (view state holds).free input = [] := List.isEmpty_iff.mp isClosed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  have named := (copy_free_all state facts holds input name).mp member
  simp [empty] at named

end MicroCFTA.SourceRecursiveIntersectionInputView
