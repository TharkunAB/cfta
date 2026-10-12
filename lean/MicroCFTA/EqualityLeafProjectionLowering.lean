import MicroCFTA.EqualityLeafProjectionProgress

/-!
# Constructor correspondence for projected leaf edits

The source constructor may remove duplicate and dead edges. The occurrence
representation retains these edges. Local source constructor equations are
sufficient to derive exact editing and required-path lowering.
-/
namespace MicroCFTA.EqualityLeafProjectionSyntax

/-- Map child positions without changing their order. -/
def mapChildren (change : Nat → Node → Node) (index : Nat) : List Node → List Node
  | [] => []
  | child :: rest => change index child :: mapChildren change (index + 1) rest

/-- Source operations used by finite leaf-only path reduction. -/
structure Source (Tag Leaf Node : Type) where
  empty : Node
  leaf : Leaf → Node
  node : List (Tag × List Node) → Node
  edit : List (Path × Leaf) → Node → Node
  require : List Path → Node → Node

/-- The source maps the original edge payloads at each child position. -/
def sourceEditEdges (source : Source Tag Leaf Node) (edits : List (Path × Leaf))
    (edges : List (Tag × List Node)) : List (Tag × List Node) :=
  edges.map fun (tag, children) =>
    (tag, mapChildren (fun index => source.edit (descendEdits edits index)) 0 children)

/-- Source required-path filtering first checks the complete original child arity. -/
def sourceRequireEdges (source : Source Tag Leaf Node) (paths : List Path)
    (edges : List (Tag × List Node)) : List (Tag × List Node) :=
  (edges.filter (fun edge => fits paths edge.2.length)).map fun (tag, children) =>
    (tag, mapChildren (fun index => source.require (descend paths index)) 0 children)

/-- These equations concern one source constructor. They do not assume any
complete reduction pass or fixed-point correspondence. They must hold also
when the constructor removes duplicate or dead supplied edges. -/
structure ConstructorLaws (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) : Prop where
  edit_empty : ∀ edits, source.edit edits source.empty = source.empty
  edit_leaf : ∀ edits value, source.edit edits (source.leaf value) = source.leaf
    (match atRoot edits with | none => value | some target => meet target value)
  edit_node : ∀ edits edges, atRoot edits = none →
    source.edit edits (source.node edges) = source.node (sourceEditEdges source edits edges)
  require_empty : ∀ paths, source.require paths source.empty = source.empty
  require_leaf : ∀ paths value, source.require paths (source.leaf value) =
    if fits paths 0 then source.leaf value else source.empty
  require_node : ∀ paths edges, source.require paths (source.node edges) =
    source.node (sourceRequireEdges source paths edges)

mutual
  /-- Lower occurrences through the canonical source constructor. -/
  def lower (source : Source Tag Leaf Node) : Tree Tag Leaf → Node
    | .empty => source.empty
    | .leaf value => source.leaf value
    | .node edges => source.node (lowerEdges source edges)

  /-- Keep all original edge occurrences in the constructor request. -/
  def lowerEdges (source : Source Tag Leaf Node) : List (Edge Tag Leaf) → List (Tag × List Node)
    | [] => []
    | .mk tag children :: rest => (tag, lowerForest source children) :: lowerEdges source rest

  /-- Lower the original ordered child positions. -/
  def lowerForest (source : Source Tag Leaf Node) : List (Tree Tag Leaf) → List Node
    | [] => []
    | child :: rest => lower source child :: lowerForest source rest
end

/-- Lowering preserves child arity even when some children are empty. -/
theorem lowerForest_length (source : Source Tag Leaf Node) (children : List (Tree Tag Leaf)) :
    (lowerForest source children).length = children.length := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp only [lowerForest, List.length_cons, ih]

/-- A node constructor cannot itself be selected by an admissible leaf edit. -/
theorem admissible_root_none (edits : List (Path × Leaf)) (edges : List (Edge Tag Leaf))
    (valid : Admissible edits (.node edges)) : atRoot edits = none := by
  unfold atRoot
  have absent : edits.find? (fun edit => edit.1.isEmpty) = none := by
    apply List.find?_eq_none.mpr
    intro entry member
    cases path : entry.1 with
    | nil =>
        have bad := valid [] entry.2 (by simpa only [← path, Prod.eta] using member)
        exact False.elim bad
    | cons head tail => simp
  rw [absent]
  rfl

/-- Selecting a child edit retains its original full path. -/
theorem descendEdits_member (edits : List (Path × Leaf)) (index : Nat) (path : Path) (target : Leaf)
    (present : (path, target) ∈ descendEdits edits index) : (index :: path, target) ∈ edits := by
  obtain ⟨⟨original, value⟩, member, found⟩ := List.mem_filterMap.mp present
  cases original with
  | nil => simp at found
  | cons head rest =>
      dsimp only at found
      split at found
      · rename_i same
        cases found
        simpa only [same] using member
      · contradiction

/-- Admissibility descends through each original child occurrence. -/
theorem admissible_children (edits : List (Path × Leaf)) (tag : Tag)
    (children : List (Tree Tag Leaf)) (rest : List (Edge Tag Leaf))
    (valid : Admissible edits (.node (.mk tag children :: rest))) :
    ∀ path target, (path, target) ∈ edits → ∀ index tail, path = index :: tail → ChildAt index tail children := by
  intro path target present index tail same
  subst path
  exact (valid _ _ present).1

mutual
  /-- Canonical lowering commutes with every admissible leaf edit. -/
  theorem edit_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf)
      (laws : ConstructorLaws source meet) (edits : List (Path × Leaf)) (tree : Tree Tag Leaf)
      (valid : Admissible edits tree) :
      lower source (edit meet edits tree) = source.edit edits (lower source tree) := by
    cases tree with
    | empty => exact (laws.edit_empty edits).symm
    | leaf value => exact (laws.edit_leaf edits value).symm
    | node edges =>
        rw [edit, lower, lower, laws.edit_node edits _ (admissible_root_none edits edges valid)]
        exact congrArg source.node (edit_edges_lower source meet laws edits edges valid)

  /-- Source normalization receives the same mapped edge payload list. -/
  theorem edit_edges_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf)
      (laws : ConstructorLaws source meet) (edits : List (Path × Leaf)) (edges : List (Edge Tag Leaf))
      (valid : Admissible edits (.node edges)) :
      lowerEdges source (editEdges meet edits edges) = sourceEditEdges source edits (lowerEdges source edges) := by
    cases edges with
    | nil => rfl
    | cons edge rest =>
        cases edge with
        | mk tag children =>
            have tailValid : Admissible edits (.node rest) := by
              intro path target present
              cases path with
              | nil => exact valid _ _ present
              | cons index path => exact (valid _ _ present).2
            have childrenValid : ∀ index path target, (index :: path, target) ∈ edits → ChildAt index path children := by
              intro index path target present
              exact (valid _ _ present).1
            simp only [editEdges, lowerEdges, sourceEditEdges, List.map_cons]
            rw [edit_children_lower source meet laws edits 0 children (by simpa using childrenValid),
              edit_edges_lower source meet laws edits rest tailValid]
            rfl

  /-- Local child equations derive the full ordered child-list correspondence. -/
  theorem edit_children_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf)
      (laws : ConstructorLaws source meet) (edits : List (Path × Leaf)) (offset : Nat)
      (children : List (Tree Tag Leaf))
      (valid : ∀ index path target, ((offset + index) :: path, target) ∈ edits → ChildAt index path children) :
      lowerForest source (editChildren meet edits offset children) =
        mapChildren (fun index => source.edit (descendEdits edits index)) offset (lowerForest source children) := by
    cases children with
    | nil => rfl
    | cons child rest =>
        have headValid : Admissible (descendEdits edits offset) child := by
          intro path target present
          exact valid 0 path target (by simpa using descendEdits_member edits offset path target present)
        have tailValid : ∀ index path target, ((offset + 1 + index) :: path, target) ∈ edits → ChildAt index path rest := by
          intro index path target present
          exact valid (index + 1) path target (by simpa [Nat.add_assoc, Nat.add_comm 1 index] using present)
        simp only [editChildren, lowerForest, mapChildren]
        rw [edit_lower source meet laws _ child headValid,
          edit_children_lower source meet laws edits (offset + 1) rest tailValid]
end

mutual
  /-- Exact required-path deletion commutes with canonical lowering. -/
  theorem require_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf)
      (laws : ConstructorLaws source meet) (paths : List Path) (tree : Tree Tag Leaf) :
      lower source (require paths tree) = source.require paths (lower source tree) := by
    cases tree with
    | empty => exact (laws.require_empty paths).symm
    | leaf value =>
        rw [require, lower, laws.require_leaf]
        split <;> rfl
    | node edges =>
        rw [require, lower, lower, laws.require_node]
        exact congrArg source.node (require_edges_lower source meet laws paths edges)

  /-- Required paths preserve the source's filter-before-map order. -/
  theorem require_edges_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf)
      (laws : ConstructorLaws source meet) (paths : List Path) (edges : List (Edge Tag Leaf)) :
      lowerEdges source (requireEdges paths edges) = sourceRequireEdges source paths (lowerEdges source edges) := by
    cases edges with
    | nil => rfl
    | cons edge rest =>
        cases edge with
        | mk tag children =>
            simp only [requireEdges, lowerEdges, sourceRequireEdges, List.filter_cons, lowerForest_length]
            split
            · simp only [lowerEdges, List.map_cons]
              rw [require_children_lower source meet laws paths 0 children,
                require_edges_lower source meet laws paths rest]
              rfl
            · exact require_edges_lower source meet laws paths rest

  /-- Source required-path recursion acts on the same ordered child positions. -/
  theorem require_children_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf)
      (laws : ConstructorLaws source meet) (paths : List Path) (index : Nat) (children : List (Tree Tag Leaf)) :
      lowerForest source (requireChildren paths index children) =
        mapChildren (fun index => source.require (descend paths index)) index (lowerForest source children) := by
    cases children with
    | nil => rfl
    | cons child rest =>
        simp only [requireChildren, lowerForest, mapChildren]
        rw [require_lower source meet laws _ child, require_children_lower source meet laws paths (index + 1) rest]
end

end MicroCFTA.EqualityLeafProjectionSyntax
