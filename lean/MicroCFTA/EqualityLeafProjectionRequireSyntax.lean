import MicroCFTA.EqualityLeafProjectionRepresentation

/-!
# Root-only requirements on original occurrences

A requirement that fits arity zero contains only root paths. It leaves the
entire original occurrence syntax unchanged, including duplicate ancestor
rows. This matches the source worker's direct-return branch.
-/
namespace MicroCFTA.EqualityLeafProjectionRequireSyntax
open EqualityLeafProjectionSyntax

/-- A requirement fitting a nullary constructor names only the current root. -/
theorem fits_zero_paths (paths : List Path) (fitsZero : fits paths 0 = true) :
    ∀ path ∈ paths, path = [] := by
  intro path member
  have accepted := List.all_eq_true.mp fitsZero path member
  cases path with
  | nil => rfl
  | cons index rest => simp at accepted

/-- Root-only requirements fit every original constructor arity. -/
theorem fits_zero_all (paths : List Path) (fitsZero : fits paths 0 = true) (arity : Nat) : fits paths arity = true := by
  apply List.all_eq_true.mpr
  intro path member
  rw [fits_zero_paths paths fitsZero path member]

/-- Root-only requirements contribute no suffix to any child position. -/
theorem descend_zero (paths : List Path) (fitsZero : fits paths 0 = true) (index : Nat) : descend paths index = [] := by
  induction paths with
  | nil => rfl
  | cons path rest ih =>
      have root : path = [] := fits_zero_paths _ fitsZero path (by simp)
      subst path
      have later : fits rest 0 = true := by simpa only [fits, List.all_cons, Bool.true_and] using fitsZero
      simpa only [descend, List.filterMap_cons] using ih later

mutual
/-- The original occurrence tree is unchanged by a root-only requirement. -/
theorem require_trivial (paths : List Path) (fitsZero : fits paths 0 = true) (tree : Tree Tag Leaf) :
    require paths tree = tree := by
  cases tree with
  | empty => rfl
  | leaf value => simp only [require, fitsZero, ↓reduceIte]
  | node edges => simp only [require, requireEdges_trivial paths fitsZero edges]
termination_by sizeOf tree

/-- Original duplicate ancestor occurrences remain unchanged in the direct-return case. -/
theorem requireEdges_trivial (paths : List Path) (fitsZero : fits paths 0 = true) (edges : List (Edge Tag Leaf)) :
    requireEdges paths edges = edges := by
  cases edges with
  | nil => rfl
  | cons edge rest =>
      cases edge with
      | mk tag children =>
          simp only [requireEdges, fits_zero_all paths fitsZero children.length, ↓reduceIte,
            requireChildren_trivial paths fitsZero 0 children, requireEdges_trivial paths fitsZero rest]
termination_by sizeOf edges

/-- Every original child position is unchanged when no requirement enters a child. -/
theorem requireChildren_trivial (paths : List Path) (fitsZero : fits paths 0 = true) (index : Nat) (children : List (Tree Tag Leaf)) :
    requireChildren paths index children = children := by
  cases children with
  | nil => rfl
  | cons child rest =>
      simp only [requireChildren, descend_zero paths fitsZero index,
        require_trivial [] rfl child, requireChildren_trivial paths fitsZero (index + 1) rest]
termination_by sizeOf children
end

end MicroCFTA.EqualityLeafProjectionRequireSyntax
