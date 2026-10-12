import MicroCFTA.EqualityLeafProjectionLeafCache
import MicroCFTA.EqualityLeafProjectionNullary
import MicroCFTA.SymbolicHashJoin

/-!
# Actual nullary source intersection and the global identity shortcut

The product reads physical edge declarations, matches their source symbols,
conjoins complete constraints, and executes the actual nullary constructors.
Canonical leaf readback derives its row product. The source identity branch
uses equality of whole leaf nodes, including all constructor symbols.
-/
namespace MicroCFTA.EqualityLeafProjectionProduct
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open InternedFreshProbeKeys GuardConjunction
open EqualityLeafProjectionLeafCache (ConstraintKey Leaf Row)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Source conjoinConstraints combines the cached equalities and canonical residual guards. -/
noncomputable def combine (left right : ConstraintKey) : ConstraintKey :=
  (SourceCompactGuards.combineEqualities left.1 right.1, merge GuardStructuralOrder.le left.2 right.2)

/-- Admitted nullary constraints remain the exact constraints of the joined row. -/
theorem combine_row (first second : Row initial) :
    combine (EqualityLeafProjectionLeafCache.constraint first) (EqualityLeafProjectionLeafCache.constraint second) =
      EqualityLeafProjectionLeafCache.constraint (EqualityLeafProjectionAdmission.join initial first second) := rfl

/-- Source operand identity ordering does not change an admitted row constraint. -/
theorem combine_row_comm (first second : Row initial) :
    combine (EqualityLeafProjectionLeafCache.constraint first) (EqualityLeafProjectionLeafCache.constraint second) =
      combine (EqualityLeafProjectionLeafCache.constraint second) (EqualityLeafProjectionLeafCache.constraint first) := by
  rw [combine_row, combine_row]
  exact congrArg EqualityLeafProjectionLeafCache.constraint ((EqualityLeafProjectionAdmission.algebra initial).comm first second)

/-- The source Cartesian leaf branch pairs exactly equal constructor symbols. -/
noncomputable def cross (left right : List (Fin symbols × ConstraintKey)) : List (Fin symbols × ConstraintKey) :=
  SymbolicHashJoin.hashJoin Prod.fst (fun first second => (first.1, combine first.2 second.2)) left right

/-- Physical candidate-pair membership retains both exact input row declarations. -/
theorem cross_member (left right : List (Fin symbols × ConstraintKey)) (row : Fin symbols × ConstraintKey) :
    row ∈ cross left right ↔ ∃ first ∈ left, ∃ second ∈ right,
      first.1 = second.1 ∧ (first.1, combine first.2 second.2) = row :=
  SymbolicHashJoin.hashJoin_member _ _ left right row

/-- Reconstruct the source declaration list from admitted abstract row occurrences. -/
noncomputable def declarations (leaf : Leaf initial symbols) : List (Fin symbols × ConstraintKey) :=
  (EqualityLeafProjectionLeafCache.choices leaf).map fun (symbol, row) =>
    (symbol, EqualityLeafProjectionLeafCache.constraint row)

/-- The admitted leaf constructor is the generic physical nullary constructor. -/
theorem leaf_build (leaf : Leaf initial symbols) :
    EqualityLeafProjectionLeafCache.build leaf = EqualityLeafProjectionNullary.build (declarations leaf) := by
  simp only [EqualityLeafProjectionLeafCache.build, EqualityLeafProjectionNullary.build,
    EqualityLeafProjectionLeafCache.requests, EqualityLeafProjectionNullary.requests, declarations, List.map_map]
  rfl

/-- Actual canonical leaf declarations have exactly the admitted occurrence membership. -/
theorem physical_declarations (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey)
    (coherent : Coherent state) (linked : Linked state) (row : Fin symbols × ConstraintKey) :
    row ∈ (nodeEdges (run (EqualityLeafProjectionLeafCache.build leaf) state).1).map EqualityLeafProjectionNullary.declaration ↔
      row ∈ declarations leaf := by
  rw [leaf_build]
  exact EqualityLeafProjectionNullary.build_declarations _ state coherent linked row

/-- Every declaration comes from exactly one admitted source guard at its symbol. -/
theorem declarations_member (leaf : Leaf initial symbols) (declaration : Fin symbols × ConstraintKey) :
    declaration ∈ declarations leaf ↔ ∃ symbol row, leaf symbol row ∧
      (symbol, EqualityLeafProjectionLeafCache.constraint row) = declaration := by
  simp only [declarations, List.mem_map]
  constructor
  · rintro ⟨⟨symbol, row⟩, member, same⟩
    exact ⟨symbol, row, (EqualityLeafProjectionLeafCache.choices_member leaf symbol row).mp member, same⟩
  · rintro ⟨symbol, row, member, same⟩
    exact ⟨(symbol, row), (EqualityLeafProjectionLeafCache.choices_member leaf symbol row).mpr member, same⟩

/-- Physical product construction reads actual source row fields and keeps their constraints. -/
noncomputable def product (left right : Value (Fin symbols) ConstraintKey) : Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  EqualityLeafProjectionNullary.build (cross ((nodeEdges left).map EqualityLeafProjectionNullary.declaration)
    ((nodeEdges right).map EqualityLeafProjectionNullary.declaration))

/-- Cartesian construction on physical leaves decodes to the exact admitted row product. -/
theorem product_read (first second : Leaf initial symbols)
    (leftState rightState state : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent state)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) (linked : Linked state) :
    EqualityLeafProjectionLeafCache.read (run (product (run (EqualityLeafProjectionLeafCache.build first) leftState).1
      (run (EqualityLeafProjectionLeafCache.build second) rightState).1) state).1 =
      fun symbol => FiniteRowIntersection.product (EqualityLeafProjectionAdmission.algebra initial) (first symbol) (second symbol) := by
  funext symbol row
  apply propext
  change (∃ edge ∈ nodeEdges (run (EqualityLeafProjectionNullary.build _) state).1,
    edge.entry.key = EqualityLeafProjectionLeafCache.key symbol row) ↔ _
  rw [EqualityLeafProjectionNullary.build_keys _ state coherent linked]
  constructor
  · rintro ⟨declaration, present, resultKey⟩
    obtain ⟨left, leftMember, right, rightMember, sameSymbol, sameResult⟩ := (cross_member _ _ declaration).mp present
    have leftMember := (physical_declarations first leftState leftCoherent leftLinked left).mp leftMember
    have rightMember := (physical_declarations second rightState rightCoherent rightLinked right).mp rightMember
    obtain ⟨leftSymbol, leftRow, leftPresent, rfl⟩ := (declarations_member first left).mp leftMember
    obtain ⟨rightSymbol, rightRow, rightPresent, rfl⟩ := (declarations_member second right).mp rightMember
    dsimp only at sameSymbol
    subst rightSymbol
    subst declaration
    rw [combine_row] at resultKey
    have joined := EqualityLeafProjectionLeafCache.key_injective leftSymbol symbol
      (EqualityLeafProjectionAdmission.join initial leftRow rightRow) row resultKey
    obtain ⟨rfl, equal⟩ := joined
    exact ⟨leftRow, rightRow, leftPresent, rightPresent, equal⟩
  · rintro ⟨leftRow, rightRow, leftPresent, rightPresent, equal⟩
    refine ⟨(symbol, EqualityLeafProjectionLeafCache.constraint (EqualityLeafProjectionAdmission.join initial leftRow rightRow)), ?_, ?_⟩
    · apply (cross_member _ _ _).mpr
      refine ⟨(symbol, EqualityLeafProjectionLeafCache.constraint leftRow), ?_,
        (symbol, EqualityLeafProjectionLeafCache.constraint rightRow), ?_, rfl, ?_⟩
      · exact (physical_declarations first leftState leftCoherent leftLinked _).mpr
          ((declarations_member first _).mpr ⟨symbol, leftRow, leftPresent, rfl⟩)
      · exact (physical_declarations second rightState rightCoherent rightLinked _).mpr
          ((declarations_member second _).mpr ⟨symbol, rightRow, rightPresent, rfl⟩)
      · rw [combine_row]
    · change EqualityLeafProjectionLeafCache.key symbol (EqualityLeafProjectionAdmission.join initial leftRow rightRow) = _
      exact congrArg (EqualityLeafProjectionLeafCache.key symbol) equal

/-- The source self shortcut compares entire physical node identities. -/
noncomputable def intersect (left right : Value (Fin symbols) ConstraintKey) : Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  if left.referenceOf = right.referenceOf then .pure left else product left right

/-- The actual physical identity branch and Cartesian branch together derive
exact source leaf intersection, with no per-symbol shortcut. -/
theorem intersect_read (first second : Leaf initial symbols)
    (leftState rightState state : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent state)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) (linked : Linked state)
    (leftGrowth : Grows (run (EqualityLeafProjectionLeafCache.build first) leftState).2 state)
    (rightGrowth : Grows (run (EqualityLeafProjectionLeafCache.build second) rightState).2 state) :
    EqualityLeafProjectionLeafCache.read (run (intersect (run (EqualityLeafProjectionLeafCache.build first) leftState).1
      (run (EqualityLeafProjectionLeafCache.build second) rightState).1) state).1 =
      FiniteLeafSymbolsProgress.intersect (EqualityLeafProjectionAdmission.algebra initial) first second := by
  have identity := EqualityLeafProjectionLeafCache.identity_iff first second leftState rightState state
    leftCoherent rightCoherent coherent leftLinked rightLinked leftGrowth rightGrowth
  by_cases same : first = second
  · have physical := identity.mpr same
    unfold intersect
    rw [ite_eq_left physical]
    change EqualityLeafProjectionLeafCache.read (run (EqualityLeafProjectionLeafCache.build first) leftState).1 = _
    rw [EqualityLeafProjectionLeafCache.build_read first leftState leftCoherent leftLinked]
    simp only [FiniteLeafSymbolsProgress.intersect, same, ↓reduceIte]
  · have physical := fun equal => same (identity.mp equal)
    unfold intersect
    rw [ite_eq_right physical]
    rw [product_read first second leftState rightState state leftCoherent rightCoherent coherent leftLinked rightLinked linked]
    simp only [FiniteLeafSymbolsProgress.intersect, same, ↓reduceIte]

end MicroCFTA.EqualityLeafProjectionProduct
