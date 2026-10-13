import MicroCFTA.EqualityNestedUnaryProduct

/-!
# Exact source intersection for nested unary endpoints

Physical complete-node identity agrees with equality of the generated row
sets. The source shortcut and operand orientation therefore implement the
projected row operation exactly. Both caches and complete values remain
explicit in the completion theorem.
-/
namespace MicroCFTA.EqualityNestedUnaryMeet
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct EqualityMergedTargetReadback

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- The same complete outgoing rows determine one exact generated row predicate. -/
theorem shape_unique (parent leaf : Fin symbols) (left right : Node initial)
    (value : Value (Fin symbols) ConstraintKey)
    (leftShape : NodeShape parent leaf left value) (rightShape : NodeShape parent leaf right value) : left = right := by
  funext row
  apply propext
  constructor
  · intro member
    obtain ⟨edge, included, shape⟩ := leftShape.complete row member
    obtain ⟨other, present, otherShape⟩ := rightShape.sound edge included
    exact (code_unique parent leaf row other edge shape otherShape).symm ▸ present
  · intro member
    obtain ⟨edge, included, shape⟩ := rightShape.complete row member
    obtain ⟨other, present, otherShape⟩ := leftShape.sound edge included
    exact (code_unique parent leaf row other edge shape otherShape).symm ▸ present

/-- Equal generated row sets determine the same canonical complete physical value. -/
theorem node_unique (parent leaf : Fin symbols) (selected : Node initial)
    (first second : Value (Fin symbols) ConstraintKey)
    (leftShape : NodeShape parent leaf selected first) (rightShape : NodeShape parent leaf selected second)
    (leftNormal : Replayable first) (rightNormal : Replayable second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (leftAvailable : Available state first) (rightAvailable : Available state second) : first = second := by
  have leftResident := resident_edges state facts.linked first leftAvailable.resident
  have rightResident := resident_edges state facts.linked second rightAvailable.resident
  apply EqualityOrdinaryReadback.keys_ext state facts.coherent first second
    (replayable_normal first leftNormal state facts leftAvailable)
    (replayable_normal second rightNormal state facts rightAvailable) leftResident rightResident
  intro key
  constructor
  · rintro ⟨edge, member, same⟩
    obtain ⟨row, selected, shape⟩ := leftShape.sound edge member
    obtain ⟨other, included, otherShape⟩ := rightShape.complete row selected
    have equal := row_unique parent leaf row edge other state facts (leftResident edge member)
      (rightResident other included) shape otherShape
    exact ⟨other, included, equal ▸ same⟩
  · rintro ⟨edge, member, same⟩
    obtain ⟨row, selected, shape⟩ := rightShape.sound edge member
    obtain ⟨other, included, otherShape⟩ := leftShape.complete row selected
    have equal := row_unique parent leaf row edge other state facts (rightResident edge member)
      (leftResident other included) shape otherShape
    exact ⟨other, included, equal ▸ same⟩

/-- The numeric source shortcut has exactly the generated whole-row-set condition. -/
theorem identity_iff (parent leaf : Fin symbols) (left right : Node initial)
    (first second : Value (Fin symbols) ConstraintKey)
    (leftShape : NodeShape parent leaf left first) (rightShape : NodeShape parent leaf right second)
    (leftNormal : Replayable first) (rightNormal : Replayable second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (leftAvailable : Available state first) (rightAvailable : Available state second) :
    first.referenceOf = second.referenceOf ↔ left = right := by
  constructor
  · intro same
    have equal := InternedFreshProbeKeys.resident_reference_injective state facts.coherent first second
      leftAvailable.resident rightAvailable.resident same
    subst second
    exact shape_unique parent leaf left right first leftShape rightShape
  · intro same
    subst right
    exact congrArg Value.referenceOf (node_unique parent leaf left first second leftShape rightShape
      leftNormal rightNormal state facts leftAvailable rightAvailable)

/-- Execute the source identity branch before the numeric orientation of Cartesian requests. -/
noncomputable def meet (first second : Value (Fin symbols) ConstraintKey) :
    Action (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  if first.referenceOf = second.referenceOf then MergedColdMerge.pure first
  else if EqualityRawLeafProduct.swap first second then product second first else product first second

/-- The exact source whole-node shortcut yields the actual projected nested narrowing operation. -/
theorem meet_complete (parent leaf : Fin symbols) (left right : Node initial)
    (first second : Value (Fin symbols) ConstraintKey)
    (leftShape : NodeShape parent leaf left first) (rightShape : NodeShape parent leaf right second)
    (leftNormal : Replayable first) (rightNormal : Replayable second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (leftAvailable : Available state first) (rightAvailable : Available state second) :
    Complete (fun _ => meet first second) state (fun after result =>
      Available after result ∧ Replayable result ∧
        NodeShape parent leaf (EqualityFixedProjectionInvariant.narrow (Join initial) left right) result) := by
  classical
  have identity := identity_iff parent leaf left right first second leftShape rightShape
    leftNormal rightNormal state facts leftAvailable rightAvailable
  unfold meet
  split
  · rename_i same
    simpa only [EqualityFixedProjectionInvariant.narrow, ite_eq_left (identity.mp same)] using
      pure_complete first state facts prepared _ (show Available state first ∧ Replayable first ∧
        NodeShape parent leaf left first from ⟨leftAvailable, leftNormal, leftShape⟩)
  · rename_i different
    have distinct : left ≠ right := fun same => different (identity.mpr same)
    simp only [EqualityFixedProjectionInvariant.narrow, ite_eq_right distinct]
    split
    · have comm := EqualityFixedProjectionInvariant.product_comm (Join initial) (join_symmetric initial) right left
      simpa only [comm] using product_complete parent leaf right left second first rightShape leftShape
        state facts prepared rightAvailable leftAvailable
    · exact product_complete parent leaf left right first second leftShape rightShape
        state facts prepared leftAvailable rightAvailable

/-- Empty source products have no row requests and return literal Empty without cache effects. -/
theorem product_empty_left (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    product .empty value state = .done .empty state := by
  simp [product, pairs, SymbolicHashJoin.hashJoin, nodeEdges,
    MergedColdMerge.map, MergedColdMerge.bind, MergedColdMerge.pure, Result.bind, MergedColdMerge.work,
    makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]

/-- An empty right operand also has no Cartesian request, regardless of left row order. -/
theorem product_empty_right (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    product value .empty state = .done .empty state := by
  have empty : pairs value .empty = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨first, second⟩ member
    have impossible := ((pairs_member value .empty first second).mp member).2.1
    simp only [nodeEdges, List.not_mem_nil] at impossible
  simp [product, empty,
    MergedColdMerge.map, MergedColdMerge.bind, MergedColdMerge.pure, Result.bind, MergedColdMerge.work,
    makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]

/-- The source Empty shortcut agrees with the complete nested intersection action. -/
theorem meet_empty_left (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    meet .empty value state = .done .empty state := by
  unfold meet
  split
  · rfl
  · split
    · exact product_empty_right value state
    · exact product_empty_left value state

/-- The second source Empty shortcut also preserves the actual cache. -/
theorem meet_empty_right (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    meet value .empty state = .done .empty state := by
  unfold meet
  split
  · rename_i same
    have empty := (EqualityLeafProjectionPhysical.reference_empty value).mp same
    subst value
    rfl
  · split
    · exact product_empty_left value state
    · exact product_empty_right value state

end MicroCFTA.EqualityNestedUnaryMeet
