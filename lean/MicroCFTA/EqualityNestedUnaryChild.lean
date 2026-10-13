import MicroCFTA.EqualityNestedUnaryCarrier
import MicroCFTA.EqualityLeafProjectionActualMeet

/-!
# Actual singleton-child intersections in the nested unary carrier

The child intersection reads complete physical rows, preserves the global
node-identity shortcut, orders unequal operands by their node identities,
and uses the source symbol join and full constraint conjunction.
Its returned key is the generated conjunction row of the two input guards.
-/
namespace MicroCFTA.EqualityNestedUnaryChild
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open EqualityNestedUnaryCarrier

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- The child has exactly the complete nullary key of one admitted canonical residual. -/
def LeafRow (symbol : Fin symbols) (row : Row initial) (value : Value (Fin symbols) ConstraintKey) : Prop :=
  ∀ key, (∃ edge ∈ nodeEdges value, edge.entry.key = key) ↔
    key = EqualityLeafProjectionLeafCache.key symbol row

/-- Singleton source construction establishes the exact physical child representation. -/
theorem build_leaf (symbol : Fin symbols) (row : Row initial) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) :
    LeafRow symbol row (run (EqualityLeafProjectionNullary.build
      [(symbol, EqualityLeafProjectionLeafCache.constraint row)]) state).1 := by
  intro key
  rw [EqualityLeafProjectionNullary.build_keys _ state facts.coherent facts.linked]
  simp only [List.mem_singleton, exists_eq_left]
  exact eq_comm

/-- Every physical source declaration of a represented child is its one declared symbol and constraint. -/
theorem declaration (symbol : Fin symbols) (row : Row initial) (value : Value (Fin symbols) ConstraintKey)
    (represented : LeafRow symbol row value) (output : Fin symbols × ConstraintKey) :
    output ∈ (nodeEdges value).map EqualityLeafProjectionNullary.declaration ↔
      output = (symbol, EqualityLeafProjectionLeafCache.constraint row) := by
  constructor
  · intro member
    obtain ⟨edge, present, same⟩ := List.mem_map.mp member
    have key := (represented edge.entry.key).mp ⟨edge, present, rfl⟩
    rw [← same]
    exact Prod.ext (congrArg EdgeKey.symbol key) (congrArg EdgeKey.constraint key)
  · intro same
    subst output
    obtain ⟨edge, present, key⟩ := (represented (EqualityLeafProjectionLeafCache.key symbol row)).mpr rfl
    exact List.mem_map.mpr ⟨edge, present, Prod.ext (congrArg EdgeKey.symbol key) (congrArg EdgeKey.constraint key)⟩

/-- Equal complete physical children encode the same canonical admitted source residual. -/
theorem represented_unique (symbol : Fin symbols) (left right : Row initial) (value : Value (Fin symbols) ConstraintKey)
    (leftRow : LeafRow symbol left value) (rightRow : LeafRow symbol right value) : left = right := by
  have key := (rightRow (EqualityLeafProjectionLeafCache.key symbol left)).mp
    ((leftRow (EqualityLeafProjectionLeafCache.key symbol left)).mpr rfl)
  exact (EqualityLeafProjectionLeafCache.key_injective symbol symbol left right key).2

/-- The actual symbol join pairs only the two represented singleton source declarations. -/
theorem cross_declaration (symbol : Fin symbols) (left right : Row initial)
    (first second : Value (Fin symbols) ConstraintKey) (leftRow : LeafRow symbol left first) (rightRow : LeafRow symbol right second)
    (output : Fin symbols × ConstraintKey) :
    output ∈ EqualityLeafProjectionProduct.cross
      ((nodeEdges first).map EqualityLeafProjectionNullary.declaration)
      ((nodeEdges second).map EqualityLeafProjectionNullary.declaration) ↔
      output = (symbol, EqualityLeafProjectionLeafCache.constraint (EqualityLeafProjectionAdmission.join initial left right)) := by
  rw [EqualityLeafProjectionProduct.cross_member]
  constructor
  · rintro ⟨leftDecl, leftMember, rightDecl, rightMember, sameSymbol, result⟩
    rw [(declaration symbol left first leftRow leftDecl).mp leftMember,
      (declaration symbol right second rightRow rightDecl).mp rightMember] at result
    simpa only [child_constraint] using result.symm
  · intro same
    refine ⟨(symbol, EqualityLeafProjectionLeafCache.constraint left), (declaration symbol left first leftRow _).mpr rfl,
      (symbol, EqualityLeafProjectionLeafCache.constraint right), (declaration symbol right second rightRow _).mpr rfl, rfl, ?_⟩
    simpa only [child_constraint] using same.symm

/-- Actual source Cartesian construction returns precisely the generated canonical child row. -/
theorem product_leaf (symbol : Fin symbols) (left right : Row initial)
    (first second : Value (Fin symbols) ConstraintKey) (leftRow : LeafRow symbol left first) (rightRow : LeafRow symbol right second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    LeafRow symbol (EqualityLeafProjectionAdmission.join initial left right)
      (run (EqualityLeafProjectionProduct.product first second) state).1 := by
  intro key
  rw [EqualityLeafProjectionProduct.product, EqualityLeafProjectionNullary.build_keys _ state facts.coherent facts.linked]
  constructor
  · rintro ⟨output, member, same⟩
    have found := (cross_declaration symbol left right first second leftRow rightRow output).mp member
    subst output
    exact same.symm
  · intro same
    refine ⟨(symbol, EqualityLeafProjectionLeafCache.constraint (EqualityLeafProjectionAdmission.join initial left right)),
      (cross_declaration symbol left right first second leftRow rightRow _).mpr rfl, same.symm⟩

/-- Preserve the actual physical whole-node shortcut and source operand orientation. -/
noncomputable def childMeet (first second : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  if first.referenceOf = second.referenceOf then .pure first
  else if EqualityRawLeafProduct.swap first second then EqualityLeafProjectionProduct.product second first
    else EqualityLeafProjectionProduct.product first second

/-- Every source child branch stays in the generated nested row carrier, including equal-identity readback. -/
theorem meet_leaf (symbol : Fin symbols) (left right : Row initial)
    (first second : Value (Fin symbols) ConstraintKey) (leftRow : LeafRow symbol left first) (rightRow : LeafRow symbol right second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (leftAvailable : Available state first) (rightAvailable : Available state second) :
    LeafRow symbol (EqualityLeafProjectionAdmission.join initial left right) (run (childMeet first second) state).1 := by
  unfold childMeet
  split
  · rename_i same
    have equal := InternedFreshProbeKeys.resident_reference_injective state facts.coherent first second
      leftAvailable.resident rightAvailable.resident same
    subst second
    have sameRow := represented_unique symbol left right first leftRow rightRow
    subst right
    have idem : EqualityLeafProjectionAdmission.join initial left left = left :=
      (EqualityLeafProjectionAdmission.algebra initial).idem left
    simpa only [run, idem] using leftRow
  · split
    · have same : EqualityLeafProjectionAdmission.join initial right left = EqualityLeafProjectionAdmission.join initial left right :=
        (EqualityLeafProjectionAdmission.algebra initial).comm right left
      simpa only [same] using product_leaf symbol right left second first rightRow leftRow state facts
    · exact product_leaf symbol left right first second leftRow rightRow state facts

/-- Actual child execution retains coherent available returned records. -/
theorem meet_available (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (leftAvailable : Available state first) :
    Facts (run (childMeet first second) state).2 ∧ Available (run (childMeet first second) state).2 (run (childMeet first second) state).1 := by
  have productFacts (left right : Value (Fin symbols) ConstraintKey) :
      Facts (run (EqualityLeafProjectionProduct.product left right) state).2 ∧
        Available (run (EqualityLeafProjectionProduct.product left right) state).2 (run (EqualityLeafProjectionProduct.product left right) state).1 := by
    have checked := EqualityLeafProjectionCompileAvailability.nullary_available
      (EqualityLeafProjectionProduct.cross ((nodeEdges left).map EqualityLeafProjectionNullary.declaration)
        ((nodeEdges right).map EqualityLeafProjectionNullary.declaration)) state
      (⟨facts.coherent, facts.cached, facts.linked⟩ : EqualityLeafProjectionCompileAvailability.Facts state)
    exact ⟨⟨checked.1.coherent, checked.1.cached, checked.1.linked⟩, checked.2⟩
  unfold childMeet
  split
  · exact ⟨facts, leftAvailable⟩
  · split <;> exact productFacts _ _

/-- A represented singleton child is structurally nonempty. -/
theorem leaf_nonempty (symbol : Fin symbols) (row : Row initial) (value : Value (Fin symbols) ConstraintKey)
    (represented : LeafRow symbol row value) : value.referenceOf ≠ .empty := by
  obtain ⟨edge, member, key⟩ := (represented (EqualityLeafProjectionLeafCache.key symbol row)).mpr rfl
  cases value <;> simp_all [nodeEdges, Value.referenceOf]

/-- Source request sequences preserve old Mu records when each request does. -/
theorem sequence_noNewMu [DecidableEq (EdgeKey Symbol Residual)]
    (requests : List (Work Symbol Residual Output))
    (unchanged : ∀ request ∈ requests, ∀ state, InternedShallowHeap.NoNewMu state (run request state).2)
    (state : State Symbol Residual) :
    InternedShallowHeap.NoNewMu state (run (EqualityLeafProjectionWorkers.sequence requests) state).2 := by
  induction requests generalizing state with
  | nil => exact InternedShallowHeap.noNewMu_refl _
  | cons first rest ih =>
      simpa only [EqualityLeafProjectionWorkers.sequence, run_bind, run] using
        InternedShallowHeap.noNewMu_trans (unchanged first List.mem_cons_self state)
          (ih (fun request member => unchanged request (List.mem_cons_of_mem _ member)) (run first state).2)

/-- The actual nullary Cartesian request sequence cannot create a Mu payload. -/
theorem product_noNewMu (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    InternedShallowHeap.NoNewMu state (run (EqualityLeafProjectionProduct.product first second) state).2 := by
  let rows := EqualityLeafProjectionProduct.cross ((nodeEdges first).map EqualityLeafProjectionNullary.declaration)
    ((nodeEdges second).map EqualityLeafProjectionNullary.declaration)
  have unchanged := sequence_noNewMu (EqualityLeafProjectionNullary.requests rows) (by
    intro request member before
    obtain ⟨⟨symbol, guard⟩, present, rfl⟩ := List.mem_map.mp member
    intro key entry body depth ordinary stored
    exact stored) state
  change InternedShallowHeap.NoNewMu state (run ((EqualityLeafProjectionWorkers.sequence
    (EqualityLeafProjectionNullary.requests rows)).bind makeNode) state).2
  rw [run_bind]
  exact InternedShallowHeap.noNewMu_trans unchanged (InternedShallowHeap.makeNode_noNewMu _ _)

/-- The source shortcut and both operand orientations preserve preparation of old Mu records. -/
theorem meet_noNewMu (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    InternedShallowHeap.NoNewMu state (run (childMeet first second) state).2 := by
  unfold childMeet
  split
  · exact InternedShallowHeap.noNewMu_refl _
  · split <;> exact product_noNewMu _ _ _

/-- Actual singleton-child Cartesian construction returns a canonical ordinary readback. -/
theorem product_normal (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) : EqualityOrdinaryReadback.Normal
      (run (EqualityLeafProjectionProduct.product first second) state).2
      (run (EqualityLeafProjectionProduct.product first second) state).1 := by
  let rows := EqualityLeafProjectionProduct.cross ((nodeEdges first).map EqualityLeafProjectionNullary.declaration)
    ((nodeEdges second).map EqualityLeafProjectionNullary.declaration)
  let built := run (EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rows)) state
  have checked := EqualityLeafProjectionNullary.completed_rows rows state facts.coherent
  have linked := EqualityLeafProjectionNullary.rows_linked rows state facts.coherent facts.linked
  have afterFacts := EqualityLeafProjectionCompileAvailability.nullary_available rows state
    (⟨facts.coherent, facts.cached, facts.linked⟩ : EqualityLeafProjectionCompileAvailability.Facts state)
  have afterCoherent : Coherent (run (makeNode built.1) built.2).2 := by
    simpa only [EqualityLeafProjectionNullary.build, run_bind] using afterFacts.1.coherent
  have normal := EqualityOrdinaryReadback.makeNode_normal built.1 built.2 _ checked.1 linked afterCoherent
    (fun edge member => (checked.2.1 edge member).1) (grows_refl _)
  simpa only [EqualityLeafProjectionProduct.product, EqualityLeafProjectionNullary.build, run_bind] using normal

/-- Exact child readback survives the source identity shortcut and both Cartesian orientations. -/
theorem meet_normal (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (normal : EqualityOrdinaryReadback.Normal state first) :
    EqualityOrdinaryReadback.Normal (run (childMeet first second) state).2 (run (childMeet first second) state).1 := by
  unfold childMeet
  split
  · exact normal
  · split <;> exact product_normal _ _ state facts

end MicroCFTA.EqualityNestedUnaryChild
