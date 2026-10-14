import MicroCFTA.SourceRecursiveIntersectionInputView

/-!
# Structural ranks from original physical payloads

Actual payload size decreases through Mu bodies, ordered row children, and
union members. Numeric allocation order supplies no structural premise.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule

/-- Rank the actual tagged payload read from the original physical maps. -/
noncomputable def weight (state : InternedConstructorTemplates.State Symbol Guard) (input : Input) : Nat := sizeOf (payload state input)

/-- Complete available records retain their exact physical structural rank. -/
theorem weight_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value) (input : Input)
    (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) : weight state input = sizeOf value :=
  congrArg sizeOf (payload_readback state facts value available input complete)

/-- The placeholder default has no larger rank than the original available record. -/
theorem weight_le (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value) : weight state (inputOf value) ≤ sizeOf value := by
  cases value with
  | empty => exact Nat.le_refl _
  | reference reference =>
      cases reference <;> simp [weight, payload, inputOf, IntersectionFlatMemoKey.input, Value.referenceOf] <;> omega
  | node entry edges depth free | union entry edges depth free | mu entry edges depth free =>
      exact Nat.le_of_eq (weight_readback state facts _ available _ rfl)

/-- An actual edge child is smaller than its complete enclosing edge record. -/
theorem edge_child_size (edge : EdgeValue Symbol Guard) (child : Value Symbol Guard) (member : child ∈ edge.children) :
    sizeOf child < sizeOf edge := by
  have inside := List.sizeOf_lt_of_mem member
  cases edge
  simp only [EdgeValue.children] at inside
  simp only [EdgeValue.mk.sizeOf_spec]
  omega

/-- The original Mu body has a smaller physical rank than its binder record. -/
theorem body_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) :
    weight state ((view state holds).body entry.identity) < weight state (.mu entry.identity) := by
  have selected := payload_readback state facts _ available (.mu entry.identity) rfl
  have bodyExact : (view state holds).body entry.identity = inputOf body := by simp only [view, selected]
  rw [bodyExact, weight_readback state facts _ available _ rfl]
  have bound := weight_le state facts body (available.children body (by simp [children]))
  simp only [Value.mu.sizeOf_spec]
  omega

/-- Every actual ordered row child has a smaller physical rank than its source node. -/
theorem row_child_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) (available : Available state (.node entry edges depth free))
    (selectedRow : Row Symbol) (present : selectedRow ∈ (view state holds).rows entry.identity)
    (input : Input) (member : input ∈ selectedRow.children) : weight state input < weight state (.node entry.identity) := by
  have selected := payload_readback state facts _ available (.node entry.identity) rfl
  have rowsExact : (view state holds).rows entry.identity = edges.map (row holds) := by simp only [view, selected]
  rw [rowsExact] at present
  obtain ⟨edge, inEdges, rfl⟩ := List.mem_map.mp present
  obtain ⟨child, inChildren, rfl⟩ := List.mem_map.mp member
  rw [weight_readback state facts _ available _ rfl]
  have bound := weight_le state facts child (available.children child (List.mem_flatMap.mpr ⟨edge, inEdges, inChildren⟩))
  have edgeBound := edge_child_size edge child inChildren
  have listBound := List.sizeOf_lt_of_mem inEdges
  simp only [Value.node.sizeOf_spec]
  omega

/-- Every actual union member has a smaller physical rank than its source union. -/
theorem member_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (entry : Interned NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (available : Available state (.union entry members depth free))
    (input : Input) (member : input ∈ (view state holds).members entry.identity) :
    weight state input < weight state (.union entry.identity) := by
  have selected := payload_readback state facts _ available (.union entry.identity) rfl
  have membersExact : (view state holds).members entry.identity = members.map inputOf := by simp only [view, selected]
  rw [membersExact] at member
  obtain ⟨child, inMembers, rfl⟩ := List.mem_map.mp member
  rw [weight_readback state facts _ available _ rfl]
  have bound := weight_le state facts child (available.children child inMembers)
  have listBound := List.sizeOf_lt_of_mem inMembers
  simp only [Value.union.sizeOf_spec]
  omega

/-- Every physical payload rank is positive, including empty defaults. -/
theorem weight_positive (state : InternedConstructorTemplates.State Symbol Guard) (input : Input) : 0 < weight state input := by
  unfold weight
  cases payload state input <;> simp <;> omega

/-- Every row in the total actual physical view strictly decreases its node's payload rank. -/
theorem rows_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (identity : Nat) (selectedRow : Row Symbol)
    (present : selectedRow ∈ (view state holds).rows identity) (input : Input) (member : input ∈ selectedRow.children) :
    weight state input < weight state (.node identity) := by
  rcases payload_selected state identity (.node identity) (.inl rfl) with absent | ⟨value, found, same, selected⟩
  · simp [view, absent] at present
  · cases value <;> simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input,
      Option.getD_some, reduceCtorEq, Input.node.injEq] at same <;> try contradiction
    case reference reference => cases reference <;> contradiction
    case node entry edges depth free =>
      subst identity
      exact row_child_weight state facts holds entry edges depth free
        (SourcePreparedSharedRows.read_available state facts _ _ found) selectedRow present input member

/-- Every union member in the total actual physical view strictly decreases its payload rank. -/
theorem members_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (identity : Nat) (input : Input)
    (member : input ∈ (view state holds).members identity) : weight state input < weight state (.union identity) := by
  rcases payload_selected state identity (.union identity) (.inr (.inr rfl)) with absent | ⟨value, found, same, selected⟩
  · simp [view, absent] at member
  · cases value <;> simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input,
      Option.getD_some, reduceCtorEq, Input.union.injEq] at same <;> try contradiction
    case reference reference => cases reference <;> contradiction
    case union entry members depth free =>
      subst identity
      exact member_weight state facts holds entry members depth free
        (SourcePreparedSharedRows.read_available state facts _ _ found) input member

/-- The actual physical payload rank supplies every local schedule decrease. -/
noncomputable def localWeight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) : LocalWeight (view state holds) :=
  structuralLocalWeight (view state holds) (weight state)
    (fun name => weight_positive state (.ref name)) (fun name => weight_positive state (.node name))
    (rows_weight state facts holds) (members_weight state facts holds)

end MicroCFTA.SourceRecursiveIntersectionInputView
