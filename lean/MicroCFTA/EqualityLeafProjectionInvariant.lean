import MicroCFTA.EqualityLeafProjectionLowering

/-!
# Leaf endpoint invariants under source occurrence edits

Path edits preserve ancestor positions. Required paths can only remove
ancestor alternatives. Every selected endpoint therefore remains a leaf
domain after either phase, even when canonical parents merge.
-/
namespace MicroCFTA.EqualityLeafProjectionSyntax

mutual
  /-- Leaf edits retain every original leaf-only endpoint property. -/
  theorem edit_leafAt (meet : Leaf → Leaf → Leaf) (edits : List (Path × Leaf))
      (path : Path) (tree : Tree Tag Leaf) (valid : LeafAt path tree) : LeafAt path (edit meet edits tree) := by
    cases tree with
    | empty => trivial
    | leaf value => cases path <;> trivial
    | node edges =>
        cases path with
        | nil => exact valid
        | cons index path => exact edit_edges_leafAt meet edits index path edges valid

  /-- Each mapped ancestor alternative retains its endpoint property. -/
  theorem edit_edges_leafAt (meet : Leaf → Leaf → Leaf) (edits : List (Path × Leaf))
      (index : Nat) (path : Path) (edges : List (Edge Tag Leaf)) (valid : LeavesAt index path edges) :
      LeavesAt index path (editEdges meet edits edges) := by
    cases edges with
    | nil => trivial
    | cons edge rest =>
        cases edge with
        | mk tag children => exact ⟨edit_children_leafAt meet edits 0 index path children valid.1,
            edit_edges_leafAt meet edits index path rest valid.2⟩

  /-- Child edits preserve arity and every original endpoint position. -/
  theorem edit_children_leafAt (meet : Leaf → Leaf → Leaf) (edits : List (Path × Leaf))
      (offset index : Nat) (path : Path) (children : List (Tree Tag Leaf)) (valid : ChildAt index path children) :
      ChildAt index path (editChildren meet edits offset children) := by
    cases children with
    | nil => trivial
    | cons child rest =>
        cases index with
        | zero => exact edit_leafAt meet (descendEdits edits offset) path child valid
        | succ index => exact edit_children_leafAt meet edits (offset + 1) index path rest valid
end

mutual
  /-- Deleting invalid ancestors cannot introduce a nonleaf selected endpoint. -/
  theorem require_leafAt (paths : List Path) (path : Path) (tree : Tree Tag Leaf)
      (valid : LeafAt path tree) : LeafAt path (require paths tree) := by
    cases tree with
    | empty => trivial
    | leaf value =>
        simp only [require]
        split <;> cases path <;> trivial
    | node edges =>
        cases path with
        | nil => exact valid
        | cons index path => exact require_edges_leafAt paths index path edges valid

  /-- Surviving required-path rows retain their original endpoint property. -/
  theorem require_edges_leafAt (paths : List Path) (index : Nat) (path : Path)
      (edges : List (Edge Tag Leaf)) (valid : LeavesAt index path edges) :
      LeavesAt index path (requireEdges paths edges) := by
    cases edges with
    | nil => trivial
    | cons edge rest =>
        cases edge with
        | mk tag children =>
            simp only [requireEdges]
            split
            · exact ⟨require_children_leafAt paths 0 index path children valid.1,
                require_edges_leafAt paths index path rest valid.2⟩
            · exact require_edges_leafAt paths index path rest valid.2

  /-- Required paths preserve child order in every retained ancestor row. -/
  theorem require_children_leafAt (paths : List Path) (offset index : Nat) (path : Path)
      (children : List (Tree Tag Leaf)) (valid : ChildAt index path children) :
      ChildAt index path (requireChildren paths offset children) := by
    cases children with
    | nil => trivial
    | cons child rest =>
        cases index with
        | zero => exact require_leafAt (descend paths offset) path child valid
        | succ index => exact require_children_leafAt paths (offset + 1) index path rest valid
end

/-- A forest path starts with an actual child index. The empty path is not edited. -/
def ForestLeafAt (path : Path) (forest : List (Tree Tag Leaf)) : Prop :=
  match path with
  | [] => True
  | index :: rest => ChildAt index rest forest

/-- All fixed selected paths end in leaf domains. -/
def Endpoints (paths : List Path) (forest : List (Tree Tag Leaf)) : Prop :=
  ∀ path ∈ paths, ForestLeafAt path forest

/-- Leaf-only endpoints persist through arbitrary leaf target edits. -/
theorem edit_endpoints (meet : Leaf → Leaf → Leaf) (edits : List (Path × Leaf))
    (paths : List Path) (forest : List (Tree Tag Leaf)) (valid : Endpoints paths forest) :
    Endpoints paths (editChildren meet edits 0 forest) := by
  intro path member
  cases path with
  | nil => trivial
  | cons index path => exact edit_children_leafAt meet edits 0 index path forest (valid _ member)

/-- Required-path filtering preserves all fixed leaf-only endpoints. -/
theorem require_endpoints (required paths : List Path) (forest : List (Tree Tag Leaf)) (valid : Endpoints paths forest) :
    Endpoints paths (requireChildren required 0 forest) := by
  intro path member
  cases path with
  | nil => trivial
  | cons index path => exact require_children_leafAt required 0 index path forest (valid _ member)

/-- Explicit root erasure satisfies every leaf-only endpoint property. -/
theorem empty_children (index : Nat) (path : Path) (forest : List (Tree Tag Leaf)) :
    ChildAt index path (forest.map (fun _ => (Tree.empty : Tree Tag Leaf))) := by
  induction forest generalizing index with
  | nil => trivial
  | cons child rest ih => cases index with
      | zero => trivial
      | succ index => exact ih index

/-- Forest-wide empty propagation also preserves the endpoint invariant. -/
theorem empty_endpoints (paths : List Path) (forest : List (Tree Tag Leaf)) :
    Endpoints paths (forest.map (fun _ => (Tree.empty : Tree Tag Leaf))) := by
  intro path member
  cases path with
  | nil => trivial
  | cons index path => exact empty_children index path forest

end MicroCFTA.EqualityLeafProjectionSyntax
