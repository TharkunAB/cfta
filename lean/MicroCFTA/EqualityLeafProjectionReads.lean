import MicroCFTA.EqualityLeafProjectionTermination

/-!
# Actual path projection into leaf occurrence domains

Projection unions only live ancestor alternatives. A dead row contributes
nothing even when its selected child is nonempty. The source projection
therefore has a leaf representation at every fixed leaf-only endpoint.
-/
namespace MicroCFTA.EqualityLeafProjectionSyntax

/-- A canonical node discards any edge that has an empty child. -/
noncomputable def live (source : Source Tag Leaf Node) (children : List Node) : Bool := by
  classical
  exact children.all (fun child => decide (child ≠ source.empty))

/-- Read one ordered source child, with EmptyNode for an absent position. -/
def readChild (empty : Node) (read : Path → Node → Node) : Nat → Path → List Node → Node
  | _, _, [] => empty
  | 0, path, child :: _ => read path child
  | index + 1, path, _ :: rest => readChild empty read index path rest

/-- Source projection sees only the live constructor alternatives. -/
noncomputable def readEdges (source : Source Tag Leaf Node) (union : Node → Node → Node)
    (read : Path → Node → Node) (index : Nat) (path : Path) : List (Tag × List Node) → Node
  | [] => source.empty
  | (_, children) :: rest =>
      if live source children then union (readChild source.empty read index path children) (readEdges source union read index path rest)
      else readEdges source union read index path rest

/-- Local source equations for path reads and leaf-domain representation. -/
structure ProjectionLaws (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf)
    (union : Node → Node → Node) (read : Path → Node → Node) : Prop where
  leaf_zero : source.leaf zero = source.empty
  leaf_join : ∀ left right, source.leaf (join left right) = union (source.leaf left) (source.leaf right)
  read_nil : ∀ node, read [] node = node
  read_empty : ∀ path, read path source.empty = source.empty
  read_leaf : ∀ index path leaf, read (index :: path) (source.leaf leaf) = source.empty
  read_node : ∀ index path edges, read (index :: path) (source.node edges) = readEdges source union read index path edges

mutual
  /-- A selected leaf projection retains all live original occurrence contributions. -/
  noncomputable def project (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf)
      (path : Path) : Tree Tag Leaf → Leaf
    | .empty => zero
    | .leaf value => match path with | [] => value | _ :: _ => zero
    | .node edges => match path with | [] => zero | index :: path => projectEdges source zero join index path edges

  /-- Dead ancestor rows are excluded before child projection. -/
  noncomputable def projectEdges (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf)
      (index : Nat) (path : Path) : List (Edge Tag Leaf) → Leaf
    | [] => zero
    | .mk _ children :: rest =>
        if live source (lowerForest source children) then
          join (projectChildren source zero join index path children) (projectEdges source zero join index path rest)
        else projectEdges source zero join index path rest

  /-- Missing positions contribute the empty leaf domain. -/
  noncomputable def projectChildren (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf) :
      Nat → Path → List (Tree Tag Leaf) → Leaf
    | _, _, [] => zero
    | 0, path, child :: _ => project source zero join path child
    | index + 1, path, _ :: rest => projectChildren source zero join index path rest
end

mutual
  /-- Every original leaf-only endpoint projects to an actual source leaf node. -/
  theorem project_lower (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf)
      (union : Node → Node → Node) (read : Path → Node → Node) (laws : ProjectionLaws source zero join union read)
      (path : Path) (tree : Tree Tag Leaf) (valid : LeafAt path tree) :
      source.leaf (project source zero join path tree) = read path (lower source tree) := by
    cases tree with
    | empty => exact laws.leaf_zero.trans (laws.read_empty path).symm
    | leaf value =>
        cases path with
        | nil => exact (laws.read_nil _).symm
        | cons index path => exact laws.leaf_zero.trans (laws.read_leaf index path value).symm
    | node edges =>
        cases path with
        | nil => exact False.elim valid
        | cons index path =>
            rw [project, lower, laws.read_node]
            exact project_edges_lower source zero join union read laws index path edges valid

  /-- Projection correspondence survives canonical duplicate and dead-edge removal. -/
  theorem project_edges_lower (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf)
      (union : Node → Node → Node) (read : Path → Node → Node) (laws : ProjectionLaws source zero join union read)
      (index : Nat) (path : Path) (edges : List (Edge Tag Leaf)) (valid : LeavesAt index path edges) :
      source.leaf (projectEdges source zero join index path edges) = readEdges source union read index path (lowerEdges source edges) := by
    cases edges with
    | nil => exact laws.leaf_zero
    | cons edge rest =>
        cases edge with
        | mk tag children =>
            simp only [projectEdges, lowerEdges, readEdges]
            split
            · rw [laws.leaf_join, project_children_lower source zero join union read laws index path children valid.1,
                project_edges_lower source zero join union read laws index path rest valid.2]
            · exact project_edges_lower source zero join union read laws index path rest valid.2

  /-- Ordered child lookup preserves the exact selected source leaf projection. -/
  theorem project_children_lower (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf)
      (union : Node → Node → Node) (read : Path → Node → Node) (laws : ProjectionLaws source zero join union read)
      (index : Nat) (path : Path) (children : List (Tree Tag Leaf)) (valid : ChildAt index path children) :
      source.leaf (projectChildren source zero join index path children) = readChild source.empty read index path (lowerForest source children) := by
    cases children with
    | nil => simpa only [projectChildren, readChild, lowerForest] using laws.leaf_zero
    | cons child rest =>
        cases index with
        | zero => exact project_lower source zero join union read laws path child valid
        | succ index => exact project_children_lower source zero join union read laws index path rest valid
end

/-- Decode only actual projected leaf nodes. Other source nodes are outside the endpoint invariant. -/
def decodedRead (source : Source Tag Leaf Node) (read : Path → Node → Node) (decode : Node → Leaf)
    (path : Path) (forest : List Node) : Leaf :=
  match path with
  | [] => decode source.empty
  | index :: rest => decode (readChild source.empty read index rest forest)

/-- Leaf-only endpoints derive the exact source read used by each target calculation. -/
theorem decodedRead_exact (source : Source Tag Leaf Node) (zero : Leaf) (join : Leaf → Leaf → Leaf)
    (union : Node → Node → Node) (read : Path → Node → Node) (laws : ProjectionLaws source zero join union read)
    (decode : Node → Leaf) (decode_leaf : ∀ value, decode (source.leaf value) = value)
    (index : Nat) (path : Path) (forest : List (Tree Tag Leaf)) (valid : ChildAt index path forest) :
    source.leaf (decodedRead source read decode (index :: path) (lowerForest source forest)) =
      readChild source.empty read index path (lowerForest source forest) := by
  have exactRead := project_children_lower source zero join union read laws index path forest valid
  simp only [decodedRead, ← exactRead, decode_leaf]

/-- Leaf representation preserves the exact first-seed source target fold. -/
theorem intersectList_exact (source : Source Tag Leaf Node) (zero : Leaf) (meet : Leaf → Leaf → Leaf)
    (nodeMeet : Node → Node → Node) (zero_exact : source.leaf zero = source.empty)
    (meet_exact : ∀ left right, source.leaf (meet left right) = nodeMeet (source.leaf left) (source.leaf right))
    (values : List Leaf) :
    source.leaf (EqualityLeafProjectionSchedule.intersectList meet zero values) =
      EqualityLeafProjectionSchedule.intersectList nodeMeet source.empty (values.map source.leaf) := by
  cases values with
  | nil => exact zero_exact
  | cons first rest =>
      simp only [EqualityLeafProjectionSchedule.intersectList, List.map_cons]
      induction rest with
      | nil => rfl
      | cons second tail ih =>
          simp only [List.foldr_cons, List.map_cons, meet_exact, ih]

/-- Selected forest paths use the ordinary indexed source projection.
The empty path is excluded by the selected-path premise below. -/
def readForest (source : Source Tag Leaf Node) (read : Path → Node → Node)
    (path : Path) (forest : List Node) : Node :=
  match path with
  | [] => source.empty
  | index :: rest => readChild source.empty read index rest forest

/-- Every target in the simultaneous source class is the actual projected intersection.
The proof derives this from leaf endpoints and local read/meet equations. -/
theorem class_targets_exact (source : Source Tag Leaf Node) (zero : Leaf) (join meet : Leaf → Leaf → Leaf)
    (union nodeMeet : Node → Node → Node) (read : Path → Node → Node)
    (laws : ProjectionLaws source zero join union read)
    (meet_exact : ∀ left right, source.leaf (meet left right) = nodeMeet (source.leaf left) (source.leaf right))
    (decode : Node → Leaf) (decode_leaf : ∀ value, decode (source.leaf value) = value)
    (paths : List Path) (nonempty : ∀ path ∈ paths, path ≠ []) (forest : List (Tree Tag Leaf))
    (valid : Endpoints paths forest) :
    (EqualityLeafProjectionSchedule.classEdits meet zero (decodedRead source read decode) paths
      (lowerForest source forest)).map (fun edit => (edit.1, source.leaf edit.2)) =
    EqualityLeafProjectionSchedule.classEdits nodeMeet source.empty (readForest source read) paths
      (lowerForest source forest) := by
  classical
  simp only [EqualityLeafProjectionSchedule.classEdits, List.map_map]
  apply List.map_congr_left
  intro selected selectedMember
  apply congrArg (selected, ·)
  rw [intersectList_exact source zero meet nodeMeet laws.leaf_zero meet_exact]
  apply congrArg (EqualityLeafProjectionSchedule.intersectList nodeMeet source.empty)
  simp only [List.map_map]
  apply List.map_congr_left
  intro path present
  have member := (List.mem_filter.mp present).1
  cases path with
  | nil => exact False.elim (nonempty [] member rfl)
  | cons index path => exact decodedRead_exact source zero join union read laws decode decode_leaf index path forest (valid _ member)

end MicroCFTA.EqualityLeafProjectionSyntax
