import MicroCFTA.EqualityNestedUnaryChild

/-!
# Physical parent-row composition for nested unary endpoints

Each source parent row has one canonical nullary child. Intersecting two
parent rows executes the actual child intersection before rebuilding the
parent. The generated row remains in the admitted finite guard carrier.
-/
namespace MicroCFTA.EqualityNestedUnaryProduct
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityMergedTargetReadback

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A complete parent row has the fixed unary symbol, Top, and one exact canonical child guard. -/
def RowShape (parent leaf : Fin symbols) (row : Row initial) (edge : EdgeValue (Fin symbols) ConstraintKey) : Prop :=
  edge.entry.key.symbol = parent ∧ edge.entry.key.constraint = (some [], .top) ∧
    ∃ child, edge.children = [child] ∧ LeafRow leaf row child ∧ Replayable child

/-- Two available canonical children with the same represented row are the same complete value. -/
theorem leaf_unique (symbol : Fin symbols) (row : Row initial)
    (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (leftAvailable : Available state first) (rightAvailable : Available state second)
    (leftRow : LeafRow symbol row first) (rightRow : LeafRow symbol row second)
    (leftNormal : Replayable first) (rightNormal : Replayable second) : first = second := by
  exact EqualityOrdinaryReadback.keys_ext state facts.coherent first second
    (replayable_normal first leftNormal state facts leftAvailable)
    (replayable_normal second rightNormal state facts rightAvailable)
    (resident_edges state facts.linked first leftAvailable.resident)
    (resident_edges state facts.linked second rightAvailable.resident)
    (fun key => (leftRow key).trans (rightRow key).symm)

/-- One source residual code determines its complete resident unary parent row. -/
theorem row_unique (parent leaf : Fin symbols) (row : Row initial)
    (first second : EdgeValue (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (leftResident : EdgeResident state first) (rightResident : EdgeResident state second)
    (leftShape : RowShape parent leaf row first) (rightShape : RowShape parent leaf row second) : first = second := by
  obtain ⟨leftSymbol, leftGuard, leftChild, leftChildren, leftRow, leftNormal⟩ := leftShape
  obtain ⟨rightSymbol, rightGuard, rightChild, rightChildren, rightRow, rightNormal⟩ := rightShape
  have leftAvailable := facts.cached.edges first.entry.key first leftResident leftChild (by simp [leftChildren])
  have rightAvailable := facts.cached.edges second.entry.key second rightResident rightChild (by simp [rightChildren])
  have childEq := leaf_unique leaf row leftChild rightChild state facts leftAvailable rightAvailable leftRow rightRow leftNormal rightNormal
  subst rightChild
  have leftFields := (facts.coherent.edges first.entry.key first leftResident).2.2
  have rightFields := (facts.coherent.edges second.entry.key second rightResident).2.2
  have same : first.entry.key = second.entry.key := by
    have symbols := leftSymbol.trans rightSymbol.symm
    have constraints := leftGuard.trans rightGuard.symm
    have children : first.entry.key.children = second.entry.key.children := by
      rw [← leftFields, ← rightFields, leftChildren, rightChildren]
    cases leftKey : first.entry.key
    cases rightKey : second.entry.key
    simp_all only
  change state.edgeRecords first.entry.key = some first at leftResident
  change state.edgeRecords second.entry.key = some second at rightResident
  rw [same] at leftResident
  exact Option.some.inj (leftResident.symm.trans rightResident)

/-- The same complete parent row cannot represent two distinct admitted residual codes. -/
theorem code_unique (parent leaf : Fin symbols) (left right : Row initial) (edge : EdgeValue (Fin symbols) ConstraintKey)
    (leftShape : RowShape parent leaf left edge) (rightShape : RowShape parent leaf right edge) : left = right := by
  obtain ⟨_, _, leftChild, leftChildren, leftRow, _⟩ := leftShape
  obtain ⟨_, _, rightChild, rightChildren, rightRow, _⟩ := rightShape
  have same : leftChild = rightChild := List.singleton_inj.mp (leftChildren.symm.trans rightChildren)
  subst rightChild
  exact represented_unique leaf left right leftChild leftRow rightRow

/-- Execute the source arity branch, ordered child requests, and full parent-constraint conjunction. -/
noncomputable def edgeMeet (first second : EdgeValue (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (EdgeValue (Fin symbols) ConstraintKey) :=
  if first.children.length = second.children.length then
    (EqualityLeafProjectionWorkers.sequence ((first.children.zip second.children).map fun pair => childMeet pair.1 pair.2)).bind
      (fun children => makeEdge first.entry.key.symbol
        (EqualityLeafProjectionProduct.combine first.entry.key.constraint second.entry.key.constraint) children)
  else makeEdge first.entry.key.symbol (some [], .top) [.empty]

/-- A successful nested parent product derives cache facts and its exact generated row code. -/
theorem edge_row (parent leaf : Fin symbols) (left right : Row initial)
    (first second : EdgeValue (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (prepared : Prepared state)
    (leftResident : EdgeResident state first) (rightResident : EdgeResident state second)
    (leftShape : RowShape parent leaf left first) (rightShape : RowShape parent leaf right second) :
    let result := run (edgeMeet first second) state
    Extension state result.2 ∧ EdgeResident result.2 result.1 ∧
      RowShape parent leaf (EqualityLeafProjectionAdmission.join initial left right) result.1 := by
  obtain ⟨leftSymbol, leftGuard, leftChild, leftChildren, leftRow, leftNormal⟩ := leftShape
  obtain ⟨rightSymbol, rightGuard, rightChild, rightChildren, rightRow, rightNormal⟩ := rightShape
  have leftAvailable := facts.cached.edges first.entry.key first leftResident leftChild (by simp [leftChildren])
  have rightAvailable := facts.cached.edges second.entry.key second rightResident rightChild (by simp [rightChildren])
  let child := run (childMeet leftChild rightChild) state
  have childFacts := meet_available leftChild rightChild state facts leftAvailable
  have childNormal := meet_normal leftChild rightChild state facts (replayable_normal leftChild leftNormal state facts leftAvailable)
  have represented := meet_leaf leaf left right leftChild rightChild leftRow rightRow state facts leftAvailable rightAvailable
  have extension : Extension state child.2 :=
    ⟨childFacts.1, prepared.preserve (meet_noNewMu leftChild rightChild state),
      (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2,
      InternedProbeProvenance.run_issued_extends _ state facts.coherent.valid⟩
  have childInputs : Values child.2 [child.1] := by
    intro value member
    simpa only [List.mem_singleton.mp member] using childFacts.2
  have verified := edge_verified parent (some [], .top) [child.1] child.2 childFacts.1 childInputs
  have built : Extension child.2 (run (makeEdge parent (some [], .top) [child.1]) child.2).2 :=
    ⟨verified.facts, extension.prepared.preserve (by intro key entry body depth ordinary stored; exact stored),
      verified.growth, verified.history⟩
  have fields := MergedPhysicalGroupEdges.makeEdge_fields child.2 childFacts.1 parent (some [], .top) [child.1] childInputs
  have exactRun : run (edgeMeet first second) state = run (makeEdge parent (some [], .top) [child.1]) child.2 := by
    simp only [edgeMeet, leftChildren, rightChildren, List.length_singleton, ↓reduceIte,
      List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil,
      EqualityLeafProjectionWorkers.sequence, run_bind, run, leftSymbol, leftGuard, rightGuard, parent_constraint]
    rfl
  rw [exactRun]
  exact ⟨extension.trans built, verified.result _ _ rfl, fields.1, fields.2.1,
    child.1, fields.2.2, represented, child.2, childFacts.1, childFacts.2, childNormal⟩

/-- Physical outgoing rows represent exactly the selected generated nested residuals. -/
structure NodeShape (parent leaf : Fin symbols) (selected : Node initial)
    (value : Value (Fin symbols) ConstraintKey) : Prop where
  sound : ∀ edge ∈ nodeEdges value, ∃ row, selected row ∧ RowShape parent leaf row edge
  complete : ∀ row, selected row → ∃ edge ∈ nodeEdges value, RowShape parent leaf row edge

/-- A represented parent row cannot be removed by source empty-child filtering. -/
theorem row_live (parent leaf : Fin symbols) (row : Row initial) (edge : EdgeValue (Fin symbols) ConstraintKey)
    (shape : RowShape parent leaf row edge) : EqualityLeafProjectionPhysical.dead edge = false := by
  obtain ⟨_, _, child, children, represented, _⟩ := shape
  have nonempty := leaf_nonempty leaf row child represented
  simp only [EqualityLeafProjectionPhysical.dead, children, List.any_cons, List.any_nil, Bool.or_false,
    beq_eq_false_iff_ne]
  exact nonempty

/-- Source hash-join requests retain each actual pair of equal-symbol outgoing rows. -/
def pairs (first second : Value (Fin symbols) ConstraintKey) :
    List (EdgeValue (Fin symbols) ConstraintKey × EdgeValue (Fin symbols) ConstraintKey) :=
  SymbolicHashJoin.hashJoin (fun edge => edge.entry.key.symbol) Prod.mk (nodeEdges first) (nodeEdges second)

/-- Source pair membership retains both original complete row payloads. -/
theorem pairs_member (first second : Value (Fin symbols) ConstraintKey)
    (left right : EdgeValue (Fin symbols) ConstraintKey) :
    (left, right) ∈ pairs first second ↔
      left ∈ nodeEdges first ∧ right ∈ nodeEdges second ∧ left.entry.key.symbol = right.entry.key.symbol := by
  rw [pairs, SymbolicHashJoin.hashJoin_member]
  constructor
  · rintro ⟨a, aMember, b, bMember, same, pair⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    exact ⟨aMember, bMember, same⟩
  · rintro ⟨leftMember, rightMember, same⟩
    exact ⟨left, leftMember, right, rightMember, same, rfl⟩

/-- Execute every actual parent-row request before final canonical node construction. -/
noncomputable def product (first second : Value (Fin symbols) ConstraintKey) :
    Action (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  MergedColdMerge.bind (MergedColdMerge.map (fun pair => MergedColdMerge.work (edgeMeet pair.1 pair.2)) (pairs first second))
    (fun edges => MergedColdMerge.work (makeNode edges))

/-- Each original input position of related lists has a returned output position. -/
theorem related_input {Input Output : Type} (relation : Input → Output → Prop)
    (inputs : List Input) (outputs : List Output) (related : Language.All₂ relation inputs outputs)
    (input : Input) (member : input ∈ inputs) : ∃ output ∈ outputs, relation input output := by
  induction related with
  | nil => contradiction
  | @cons first value rest remaining head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨value, List.mem_cons_self, head⟩
      · obtain ⟨output, included, property⟩ := ih member
        exact ⟨output, List.mem_cons_of_mem _ included, property⟩

/-- Complete physical Cartesian execution derives the exact generated nested row product. -/
theorem product_complete (parent leaf : Fin symbols) (left right : Node initial)
    (first second : Value (Fin symbols) ConstraintKey)
    (leftShape : NodeShape parent leaf left first) (rightShape : NodeShape parent leaf right second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (leftAvailable : Available state first) (rightAvailable : Available state second) :
    Complete (fun _ => product first second) state (fun after result =>
      Available after result ∧ Replayable result ∧
        NodeShape parent leaf (EqualityFixedProjectionInvariant.product (Join initial) left right) result) := by
  let pre := fun (before : State (Fin symbols) ConstraintKey)
      (pair : EdgeValue (Fin symbols) ConstraintKey × EdgeValue (Fin symbols) ConstraintKey) =>
    EdgeResident before pair.1 ∧ EdgeResident before pair.2 ∧
      ∃ a b : Row initial, RowShape parent leaf a pair.1 ∧ RowShape parent leaf b pair.2
  let post := fun (after : State (Fin symbols) ConstraintKey)
      (pair : EdgeValue (Fin symbols) ConstraintKey × EdgeValue (Fin symbols) ConstraintKey) (edge : EdgeValue (Fin symbols) ConstraintKey) =>
    EdgeResident after edge ∧ ∀ a b : Row initial, RowShape parent leaf a pair.1 → RowShape parent leaf b pair.2 →
      RowShape parent leaf (EqualityLeafProjectionAdmission.join initial a b) edge
  have mapped := MergedColdMergeSoundness.map_related (fun _ pair => MergedColdMerge.work (edgeMeet pair.1 pair.2)) pre post
    (fun before after extension pair valid =>
      ⟨edge_grows before after extension.growth pair.1 valid.1,
        edge_grows before after extension.growth pair.2 valid.2.1, valid.2.2⟩)
    (fun before after extension pair edge valid =>
      ⟨edge_grows before after extension.growth edge valid.1, valid.2⟩)
    (pairs first second) (fun pair member before facts prepared valid => by
      obtain ⟨a, b, aShape, bShape⟩ := valid.2.2
      have checked := edge_row parent leaf a b pair.1 pair.2 before facts prepared valid.1 valid.2.1 aShape bShape
      refine ⟨0, (run (edgeMeet pair.1 pair.2) before).1, (run (edgeMeet pair.1 pair.2) before).2,
        fun _ _ => rfl, checked.1, checked.2.1, ?_⟩
      intro otherA otherB otherLeft otherRight
      have sameA := code_unique parent leaf a otherA pair.1 aShape otherLeft
      have sameB := code_unique parent leaf b otherB pair.2 bShape otherRight
      subst otherA otherB
      exact checked.2.2)
    state facts prepared (by
      intro pair member
      have original := (pairs_member first second pair.1 pair.2).mp member
      obtain ⟨a, _, aShape⟩ := leftShape.sound pair.1 original.1
      obtain ⟨b, _, bShape⟩ := rightShape.sound pair.2 original.2.1
      exact ⟨resident_edges state facts.linked first leftAvailable.resident pair.1 original.1,
        resident_edges state facts.linked second rightAvailable.resident pair.2 original.2.1, a, b, aShape, bShape⟩)
  apply bind_complete _ _ state _ _ mapped
  intro edges middle extension related
  have resident : Edges middle edges := EnumerationSoundness.all₂_outputs _ _ _ (related.imp (fun _ _ valid => valid.1))
  have sound : ∀ edge ∈ edges, ∃ row,
      EqualityFixedProjectionInvariant.product (Join initial) left right row ∧ RowShape parent leaf row edge := by
    intro edge member
    obtain ⟨pair, pairMember, valid⟩ := EqualityMergedTargetShape.related_member _ _ _ related edge member
    have original := (pairs_member first second pair.1 pair.2).mp pairMember
    obtain ⟨a, aMember, aShape⟩ := leftShape.sound pair.1 original.1
    obtain ⟨b, bMember, bShape⟩ := rightShape.sound pair.2 original.2.1
    exact ⟨EqualityLeafProjectionAdmission.join initial a b, ⟨a, b, aMember, bMember, rfl⟩, valid.2 a b aShape bShape⟩
  have complete : ∀ row, EqualityFixedProjectionInvariant.product (Join initial) left right row →
      ∃ edge ∈ edges, RowShape parent leaf row edge := by
    rintro row ⟨a, b, aMember, bMember, same⟩
    obtain ⟨leftEdge, leftMember, aShape⟩ := leftShape.complete a aMember
    obtain ⟨rightEdge, rightMember, bShape⟩ := rightShape.complete b bMember
    have pairMember := (pairs_member first second leftEdge rightEdge).mpr
      ⟨leftMember, rightMember, aShape.1.trans bShape.1.symm⟩
    obtain ⟨edge, member, valid⟩ := related_input _ _ _ related (leftEdge, rightEdge) pairMember
    exact ⟨edge, member, same ▸ valid.2 a b aShape bShape⟩
  have verified := node_verified edges middle extension.facts resident
  let result := run (makeNode edges) middle
  have resultFacts : Facts result.2 := verified.facts
  have resultAvailable : Available result.2 result.1 := verified.result _ _ rfl
  have normal := EqualityOrdinaryReadback.makeNode_normal edges middle result.2 extension.facts.coherent extension.facts.linked
    resultFacts.coherent resident (grows_refl _)
  have edgeMembership : ∀ edge, edge ∈ nodeEdges result.1 ↔ edge ∈ edges := by
    intro edge
    rw [EqualityLeafProjectionPhysical.makeNode_edges _ middle extension.facts.coherent extension.facts.linked resident,
      EqualityLeafProjectionPhysical.normalized_member middle extension.facts.coherent edges resident edge]
    constructor
    · exact And.left
    · intro member
      obtain ⟨row, _, shape⟩ := sound edge member
      exact ⟨member, row_live parent leaf row edge shape⟩
  apply MergedColdMergeSoundness.work_post _ middle extension.prepared Available _ verified (makeNode_noNewMu _ _)
  refine ⟨resultAvailable, ⟨result.2, resultFacts, resultAvailable, normal⟩, ?_⟩
  constructor
  · exact fun edge member => sound edge ((edgeMembership edge).mp member)
  · intro row member
    obtain ⟨edge, included, shape⟩ := complete row member
    exact ⟨edge, (edgeMembership edge).mpr included, shape⟩

end MicroCFTA.EqualityNestedUnaryProduct
