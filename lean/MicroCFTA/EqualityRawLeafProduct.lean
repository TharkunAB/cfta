import MicroCFTA.EqualityRawLeafIdentity

/-!
# Raw physical leaf intersection

The source Cartesian branch reads the stored complete rows. It preserves
the hash-join pair order, conjoins residual guards, and runs every checked
edge request. The global identity branch keeps original raw syntax. The
ordinary Cartesian branch orders both operands by their node identities.
-/
namespace MicroCFTA.EqualityRawLeafProduct
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedFreshProbeKeys InternedEdgeResidency GuardConjunction
open EqualityRawLeafConstruction EqualityRawLeafIdentity

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Read the original symbol and residual from a complete physical edge. -/
def declaration (edge : EdgeValue Symbol ConstraintKey) : Symbol × Guard Formula :=
  (edge.entry.key.symbol, edge.entry.key.constraint.2)

/-- Physical declaration readback has exactly the accepted raw source membership. -/
theorem physical_declarations [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (state : State Symbol ConstraintKey) (coherent : Coherent state) (linked : Linked state)
    (row : Symbol × Guard Formula) :
    row ∈ (nodeEdges (run (build rows) state).1).map declaration ↔ row ∈ rows ∧ accepted row.2 = true := by
  constructor
  · intro member
    obtain ⟨edge, present, same⟩ := List.mem_map.mp member
    obtain ⟨original, member, admitted, originalKey⟩ :=
      (build_keys rows state coherent linked edge.entry.key).mp ⟨edge, present, rfl⟩
    have fields : original = declaration edge := Prod.ext (congrArg EdgeKey.symbol originalKey)
      (congrArg (fun key => key.constraint.2) originalKey)
    exact (fields.trans same) ▸ ⟨member, admitted⟩
  · intro present
    obtain ⟨edge, member, same⟩ := (build_member rows state coherent linked row).mpr present
    exact List.mem_map.mpr ⟨edge, member, Prod.ext (congrArg EdgeKey.symbol same)
      (congrArg (fun key => key.constraint.2) same)⟩

/-- Every physical input row retains the empty stored equality field exactly. -/
theorem physical_constraint [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (state : State Symbol ConstraintKey) (coherent : Coherent state) (linked : Linked state)
    (edge : EdgeValue Symbol ConstraintKey) (member : edge ∈ nodeEdges (run (build rows) state).1) :
    edge.entry.key.constraint = (some [], edge.entry.key.constraint.2) := by
  obtain ⟨row, _, _, same⟩ := (build_keys rows state coherent linked edge.entry.key).mp ⟨edge, member, rfl⟩
  have fields := congrArg EdgeKey.constraint same
  rw [← fields]
  rfl

/-- Actual full constraint conjunction retains that empty field and merges both residuals. -/
theorem combine_empty (first second : Guard Formula) :
    EqualityLeafProjectionProduct.combine (some [], first) (some [], second) =
      (some [], merge GuardStructuralOrder.le first second) := rfl

/-- Match complete constructor symbols with the source's reversed right buckets. -/
def cross (left right : List (Fin symbols × Guard Formula)) : List (Fin symbols × Guard Formula) :=
  SymbolicHashJoin.hashJoin Prod.fst
    (fun first second => (first.1, merge GuardStructuralOrder.le first.2 second.2)) left right

/-- Every actual Cartesian request is one pair of equal-symbol source rows. -/
theorem cross_member (left right : List (Fin symbols × Guard Formula)) (row : Fin symbols × Guard Formula) :
    row ∈ cross left right ↔ ∃ first ∈ left, ∃ second ∈ right,
      first.1 = second.1 ∧ (first.1, merge GuardStructuralOrder.le first.2 second.2) = row :=
  SymbolicHashJoin.hashJoin_member _ _ left right row

/-- Source Cartesian execution includes checked constructors for every joined row. -/
noncomputable def product (left right : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  build (cross ((nodeEdges left).map declaration) ((nodeEdges right).map declaration))

/-- Atom certificates do not change physical raw declaration membership. -/
theorem declarations_member (rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (row : Fin symbols × Guard Formula) :
    (row ∈ declarations rows ∧ accepted row.2 = true) ↔
      ∃ symbol raw, denote rows symbol raw ∧ (symbol, raw.val) = row := by
  constructor
  · rintro ⟨member, admitted⟩
    obtain ⟨⟨symbol, raw⟩, present, rfl⟩ := List.mem_map.mp member
    exact ⟨symbol, raw, ⟨present, admitted⟩, rfl⟩
  · rintro ⟨symbol, raw, ⟨member, admitted⟩, rfl⟩
    exact ⟨List.mem_map.mpr ⟨(symbol, raw), member, rfl⟩, admitted⟩

/-- Physical Cartesian readback derives the full raw guard product and source rejection. -/
theorem product_read (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (leftState rightState state : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent state)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) (linked : Linked state) :
    read (run (product (run (build (declarations first)) leftState).1
      (run (build (declarations second)) rightState).1) state).1 =
      SourceNoncanonicalLeafProgress.product (denote first) (denote second) := by
  funext symbol row
  apply propext
  change (∃ edge ∈ nodeEdges (run (build _) state).1, edge.entry.key = key (symbol, row.val)) ↔ _
  rw [build_member _ state coherent linked]
  constructor
  · rintro ⟨present, admitted⟩
    obtain ⟨left, leftMember, right, rightMember, sameSymbol, sameResult⟩ := (cross_member _ _ _).mp present
    obtain ⟨leftSymbol, leftRow, leftPresent, rfl⟩ := (declarations_member first left).mp
      ((physical_declarations _ leftState leftCoherent leftLinked left).mp leftMember)
    obtain ⟨rightSymbol, rightRow, rightPresent, rfl⟩ := (declarations_member second right).mp
      ((physical_declarations _ rightState rightCoherent rightLinked right).mp rightMember)
    dsimp only at sameSymbol
    subst rightSymbol
    obtain ⟨rfl, guardSame⟩ := Prod.mk.inj sameResult
    exact ⟨leftRow, rightRow, leftPresent, rightPresent, Subtype.ext guardSame, (accepted_iff row.val).mp admitted⟩
  · rintro ⟨leftRow, rightRow, leftPresent, rightPresent, same, admitted⟩
    refine ⟨(cross_member _ _ _).mpr ⟨(symbol, leftRow.val), ?_, (symbol, rightRow.val), ?_, rfl, ?_⟩,
      (accepted_iff row.val).mpr admitted⟩
    · exact (physical_declarations _ leftState leftCoherent leftLinked _).mpr
        ((declarations_member first _).mpr ⟨symbol, leftRow, leftPresent, rfl⟩)
    · exact (physical_declarations _ rightState rightCoherent rightLinked _).mpr
        ((declarations_member second _).mpr ⟨symbol, rightRow, rightPresent, rfl⟩)
    · exact Prod.ext rfl (congrArg Subtype.val same)

/-- The source orders ordinary operands by their interned node identities. -/
def swap (left right : Value (Fin symbols) ConstraintKey) : Bool :=
  match left, right with
  | .node first _ _ _, .node second _ _ _ => decide (second.identity < first.identity)
  | _, _ => false

/-- The Cartesian branch retains the exact source operand and hash-join request order. -/
noncomputable def orderedProduct (left right : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  if swap left right then product right left else product left right

/-- Empty left operands issue no Cartesian row or node-cache request. -/
theorem product_empty_left (value : Value (Fin symbols) ConstraintKey) : product .empty value = .pure .empty := by
  unfold product cross
  rw [SymbolicHashJoin.hashJoin_exact]
  simp [nodeEdges, build, requests, EqualityLeafProjectionWorkers.sequence, Work.bind,
    makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds]

/-- Empty right operands issue no Cartesian row or node-cache request. -/
theorem product_empty_right (value : Value (Fin symbols) ConstraintKey) : product value .empty = .pure .empty := by
  have noPairs : cross ((nodeEdges value).map declaration) [] = [] := by
    unfold cross
    rw [SymbolicHashJoin.hashJoin_exact]
    apply List.flatMap_eq_nil_iff.mpr
    intro row _
    simp
  change build (cross ((nodeEdges value).map declaration) []) = _
  rw [noPairs]
  simp [build, requests, EqualityLeafProjectionWorkers.sequence, Work.bind,
    makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds]

/-- Node-identity orientation changes no decoded Cartesian result. -/
theorem orderedProduct_read (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (leftState rightState state : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent state)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) (linked : Linked state) :
    read (run (orderedProduct (run (build (declarations first)) leftState).1
      (run (build (declarations second)) rightState).1) state).1 =
      SourceNoncanonicalLeafProgress.product (denote first) (denote second) := by
  unfold orderedProduct
  split
  · rw [product_read second first rightState leftState state rightCoherent leftCoherent coherent rightLinked leftLinked linked]
    exact SourceNoncanonicalLeafProgress.product_comm _ _
  · exact product_read first second leftState rightState state leftCoherent rightCoherent coherent leftLinked rightLinked linked

/-- The source shortcut compares complete physical node identities. -/
noncomputable def intersect (left right : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  if left.referenceOf = right.referenceOf then .pure left else orderedProduct left right

/-- The expanded model agrees with the source's first empty-left branch without allocation. -/
theorem intersect_empty_left (value : Value (Fin symbols) ConstraintKey) : intersect .empty value = .pure .empty := by
  unfold intersect
  split
  · rfl
  · simp only [orderedProduct, swap, Bool.false_eq_true, ↓reduceIte, product_empty_left]

/-- The expanded model agrees with the source's first empty-right branch without allocation. -/
theorem intersect_empty_right (value : Value (Fin symbols) ConstraintKey) : intersect value .empty = .pure .empty := by
  unfold intersect
  split
  · rename_i same
    have empty : value = .empty := (EqualityLeafProjectionPhysical.reference_empty value).mp same
    subst value
    rfl
  · cases value <;> simp only [orderedProduct, swap, Bool.false_eq_true, ↓reduceIte, product_empty_right]

/-- Closed ordinary nodes use the source identity test and ascending operand orientation. -/
theorem intersect_nodes (left right : Cache.Interned InternedBinderProtocol.NodeKey)
    (leftEdges rightEdges : List (EdgeValue (Fin symbols) ConstraintKey)) (leftDepth rightDepth : Nat) :
    intersect (.node left leftEdges leftDepth []) (.node right rightEdges rightDepth []) =
      if left.identity = right.identity then .pure (.node left leftEdges leftDepth []) else
        if right.identity < left.identity then product (.node right rightEdges rightDepth []) (.node left leftEdges leftDepth [])
        else product (.node left leftEdges leftDepth []) (.node right rightEdges rightDepth []) := by
  simp [intersect, orderedProduct, swap, Value.referenceOf]

/-- Both physical source branches agree with the raw normalization-phase operation. -/
theorem intersect_read (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (leftState rightState state : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent state)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) (linked : Linked state)
    (leftGrowth : Grows (run (build (declarations first)) leftState).2 state)
    (rightGrowth : Grows (run (build (declarations second)) rightState).2 state) :
    read (run (intersect (run (build (declarations first)) leftState).1
      (run (build (declarations second)) rightState).1) state).1 =
      SourceNoncanonicalLeafProgress.intersect (denote first) (denote second) := by
  have identity := raw_identity_iff first second leftState rightState state
    leftCoherent rightCoherent coherent leftLinked rightLinked leftGrowth rightGrowth
  by_cases same : denote first = denote second
  · have physical := identity.mpr same
    unfold intersect
    rw [ite_eq_left physical]
    change read (run (build (declarations first)) leftState).1 = _
    rw [build_read first leftState leftCoherent leftLinked]
    change denote first = _
    simp only [SourceNoncanonicalLeafProgress.intersect, same, ↓reduceIte]
  · have physical := fun equal => same (identity.mp equal)
    unfold intersect
    rw [ite_eq_right physical]
    rw [orderedProduct_read first second leftState rightState state leftCoherent rightCoherent coherent leftLinked rightLinked linked]
    simp only [SourceNoncanonicalLeafProgress.intersect, same, ↓reduceIte]

end MicroCFTA.EqualityRawLeafProduct
