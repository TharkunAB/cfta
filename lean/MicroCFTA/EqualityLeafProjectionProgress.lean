import MicroCFTA.EqualityLeafProjectionSyntax

/-!
# Progress of projected leaf edits and required paths

Each leaf occurrence uses its own finite row potential. Ancestor rows only
map their existing children or disappear. The sum counts original
occurrences before canonical source duplicate removal.
-/
namespace MicroCFTA.EqualityLeafProjectionSyntax

mutual
  /-- Arbitrary projected targets improve each leaf while retaining the ancestor structure. -/
  theorem edit_progress (rank : Leaf → Nat) (meet : Leaf → Leaf → Leaf)
      (leafProgress : ∀ target before, Progress rank (meet target before) before)
      (edits : List (Path × Leaf)) (tree : Tree Tag Leaf) :
      Progress (weight rank) (edit meet edits tree) tree := by
    cases tree with
    | empty => exact progress_refl _ _
    | leaf value =>
        cases found : atRoot edits with
        | none => simpa only [edit, found] using progress_refl (weight rank) (Tree.leaf value : Tree Tag Leaf)
        | some target =>
            have progress := leafProgress target value
            refine ⟨by simpa only [edit, found, weight] using Nat.add_le_add_right progress.1 1, ?_⟩
            intro same
            have equal : rank (meet target value) = rank value := by simpa only [edit, found, weight, Nat.add_right_cancel_iff] using same
            simp only [edit, found, progress.2 equal]
    | node edges =>
        have progress := edit_edges_progress rank meet leafProgress edits edges
        refine ⟨Nat.add_le_add_right progress.1 1, fun same => ?_⟩
        exact congrArg Tree.node (progress.2 (Nat.add_right_cancel same))

  /-- Every original edge remains in the same position during path editing. -/
  theorem edit_edges_progress (rank : Leaf → Nat) (meet : Leaf → Leaf → Leaf)
      (leafProgress : ∀ target before, Progress rank (meet target before) before)
      (edits : List (Path × Leaf)) (edges : List (Edge Tag Leaf)) :
      Progress (edgesWeight rank) (editEdges meet edits edges) edges := by
    cases edges with
    | nil => exact progress_refl _ _
    | cons edge rest =>
        cases edge with
        | mk tag children =>
            have head := edit_children_progress rank meet leafProgress edits 0 children
            have tail := edit_edges_progress rank meet leafProgress edits rest
            have hle := head.1
            have tle := tail.1
            refine ⟨by simp only [editEdges, edgesWeight]; omega, fun same => ?_⟩
            simp only [editEdges, edgesWeight] at same
            have heq : forestWeight rank (editChildren meet edits 0 children) = forestWeight rank children := by omega
            have teq : edgesWeight rank (editEdges meet edits rest) = edgesWeight rank rest := by omega
            simp only [editEdges, head.2 heq, tail.2 teq]

  /-- Child positions preserve their independent progress even when projections overlap. -/
  theorem edit_children_progress (rank : Leaf → Nat) (meet : Leaf → Leaf → Leaf)
      (leafProgress : ∀ target before, Progress rank (meet target before) before)
      (edits : List (Path × Leaf)) (index : Nat) (children : List (Tree Tag Leaf)) :
      Progress (forestWeight rank) (editChildren meet edits index children) children := by
    cases children with
    | nil => exact progress_refl _ _
    | cons child rest =>
        have head := edit_progress rank meet leafProgress (descendEdits edits index) child
        have tail := edit_children_progress rank meet leafProgress edits (index + 1) rest
        have hle := head.1
        have tle := tail.1
        refine ⟨by simp only [editChildren, forestWeight]; omega, fun same => ?_⟩
        simp only [editChildren, forestWeight] at same
        have heq : weight rank (edit meet (descendEdits edits index) child) = weight rank child := by omega
        have teq : forestWeight rank (editChildren meet edits (index + 1) rest) = forestWeight rank rest := by omega
        simp only [editChildren, head.2 heq, tail.2 teq]
end

mutual
  /-- Required paths improve the representation even when they erase complete ancestor rows. -/
  theorem require_progress (rank : Leaf → Nat) (paths : List Path) (tree : Tree Tag Leaf) :
      Progress (weight rank) (require paths tree) tree := by
    cases tree with
    | empty => exact progress_refl _ _
    | leaf value =>
        cases valid : fits paths 0
        · refine ⟨by simp [require, valid, weight], fun same => ?_⟩
          simp [require, valid, weight] at same
        · simpa only [require, valid, ↓reduceIte] using progress_refl (weight rank) (Tree.leaf value : Tree Tag Leaf)
    | node edges =>
        have progress := require_edges_progress rank paths edges
        exact ⟨Nat.add_le_add_right progress.1 1, fun same => congrArg Tree.node (progress.2 (Nat.add_right_cancel same))⟩

  /-- Removing an invalid ancestor row strictly decreases its positive contribution. -/
  theorem require_edges_progress (rank : Leaf → Nat) (paths : List Path) (edges : List (Edge Tag Leaf)) :
      Progress (edgesWeight rank) (requireEdges paths edges) edges := by
    cases edges with
    | nil => exact progress_refl _ _
    | cons edge rest =>
        cases edge with
        | mk tag children =>
            have head := require_children_progress rank paths 0 children
            have tail := require_edges_progress rank paths rest
            have hle := head.1
            have tle := tail.1
            cases valid : fits paths children.length
            · refine ⟨by simp only [requireEdges, valid, Bool.false_eq_true, ↓reduceIte, edgesWeight]; omega, fun same => ?_⟩
              simp only [requireEdges, valid, Bool.false_eq_true, ↓reduceIte, edgesWeight] at same
              omega
            · refine ⟨by simp only [requireEdges, valid, ↓reduceIte, edgesWeight]; omega, fun same => ?_⟩
              simp only [requireEdges, valid, ↓reduceIte, edgesWeight] at same
              have heq : forestWeight rank (requireChildren paths 0 children) = forestWeight rank children := by omega
              have teq : edgesWeight rank (requireEdges paths rest) = edgesWeight rank rest := by omega
              simp only [requireEdges, valid, ↓reduceIte, head.2 heq, tail.2 teq]

  /-- Requirement propagation never adds a child occurrence. -/
  theorem require_children_progress (rank : Leaf → Nat) (paths : List Path)
      (index : Nat) (children : List (Tree Tag Leaf)) :
      Progress (forestWeight rank) (requireChildren paths index children) children := by
    cases children with
    | nil => exact progress_refl _ _
    | cons child rest =>
        have head := require_progress rank (descend paths index) child
        have tail := require_children_progress rank paths (index + 1) rest
        have hle := head.1
        have tle := tail.1
        refine ⟨by simp only [requireChildren, forestWeight]; omega, fun same => ?_⟩
        simp only [requireChildren, forestWeight] at same
        have heq : weight rank (require (descend paths index) child) = weight rank child := by omega
        have teq : forestWeight rank (requireChildren paths (index + 1) rest) = forestWeight rank rest := by omega
        simp only [requireChildren, head.2 heq, tail.2 teq]
end

/-- A source root becomes explicitly empty during forest-wide empty propagation. -/
theorem empty_progress (rank : Leaf → Nat) (tree : Tree Tag Leaf) : Progress (weight rank) .empty tree := by
  cases tree <;> simp [Progress, weight]

/-- Sum the finite source potential over all constructor symbols at one leaf. -/
noncomputable def leafRank (algebra : FiniteRowIntersection.Conjunction Row) (inventory : List Row)
    (leaf : FiniteLeafSymbolsProgress.Node Row symbols) : Nat :=
  ((List.ofFn id : List (Fin symbols)).map (fun symbol => FiniteLeafForestProgress.potential algebra inventory (leaf symbol))).sum

/-- The exact global source self shortcut supplies the local leaf progress premise. -/
theorem source_leaf_progress (algebra : FiniteRowIntersection.Conjunction Row) (inventory : List Row)
    (complete : ∀ row, row ∈ inventory) (target before : FiniteLeafSymbolsProgress.Node Row symbols) :
    Progress (leafRank algebra inventory) (FiniteLeafSymbolsProgress.intersect algebra target before) before := by
  rw [FiniteLeafSymbolsProgress.intersect_comm]
  have progress := FiniteLeafForestProgress.sum_progress algebra inventory (List.ofFn id : List (Fin symbols))
    before (FiniteLeafSymbolsProgress.intersect algebra before target)
    (fun symbol _ => FiniteLeafSymbolsProgress.intersect_improves algebra inventory complete before target symbol)
  refine ⟨progress.1, fun same => ?_⟩
  funext symbol
  exact progress.2 same symbol (by simp)

end MicroCFTA.EqualityLeafProjectionSyntax
