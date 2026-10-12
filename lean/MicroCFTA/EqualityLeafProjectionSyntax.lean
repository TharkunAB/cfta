import MicroCFTA.FiniteLeafSymbolsProgress

/-!
# Occurrence trees for equality edits at leaf domains

An occurrence tree retains the original ancestor alternatives. Different
occurrences can lower to the same canonical source edge. Leaf edits change
only leaf payloads. Required paths can remove ancestor alternatives.
-/
namespace MicroCFTA.EqualityLeafProjectionSyntax

abbrev Path := List Nat

mutual
  /-- A finite source occurrence has an explicit empty case and a leaf domain. -/
  inductive Tree (Tag Leaf : Type) where
    | empty
    | leaf (value : Leaf)
    | node (edges : List (Edge Tag Leaf))

  /-- An ancestor edge retains its source label and ordered child occurrences. -/
  inductive Edge (Tag Leaf : Type) where
    | mk (tag : Tag) (children : List (Tree Tag Leaf))
end

/-- The source payload of an ancestor edge remains unchanged by leaf edits. -/
def Edge.tag : Edge Tag Leaf → Tag
  | .mk tag _ => tag

/-- Child order is part of the ancestor skeleton. -/
def Edge.children : Edge Tag Leaf → List (Tree Tag Leaf)
  | .mk _ children => children

/-- Retain the suffixes of selected paths below one child position. -/
def descend (paths : List Path) (index : Nat) : List Path :=
  paths.filterMap fun path => match path with
    | [] => none
    | head :: rest => if head = index then some rest else none

/-- Empty paths name the current node and impose no child requirement. -/
def fits (paths : List Path) (arity : Nat) : Bool :=
  paths.all fun path => match path with
    | [] => true
    | index :: _ => index < arity

/-- A source leaf meets the first edit at its own path. Descendant edits have no child to change. -/
def atRoot (edits : List (Path × Leaf)) : Option Leaf :=
  (edits.find? (fun edit => edit.1.isEmpty)).map Prod.snd

/-- Keep the path edits that reach one child. -/
def descendEdits (edits : List (Path × Leaf)) (index : Nat) : List (Path × Leaf) :=
  edits.filterMap fun (path, target) => match path with
    | [] => none
    | head :: rest => if head = index then some (rest, target) else none

mutual
  /-- Edit leaf occurrences without adding an ancestor alternative. -/
  def edit (meet : Leaf → Leaf → Leaf) (edits : List (Path × Leaf)) : Tree Tag Leaf → Tree Tag Leaf
    | .empty => .empty
    | .leaf value => .leaf (match atRoot edits with | none => value | some target => meet target value)
    | .node edges => .node (editEdges meet edits edges)

  /-- Apply all selected child edits to the original ancestor edge list. -/
  def editEdges (meet : Leaf → Leaf → Leaf) (edits : List (Path × Leaf)) :
      List (Edge Tag Leaf) → List (Edge Tag Leaf)
    | [] => []
    | .mk tag children :: rest =>
        .mk tag (editChildren meet edits 0 children) :: editEdges meet edits rest

  /-- Source child positions use the original ordered child list. -/
  def editChildren (meet : Leaf → Leaf → Leaf) (edits : List (Path × Leaf)) (index : Nat) :
      List (Tree Tag Leaf) → List (Tree Tag Leaf)
    | [] => []
    | child :: rest => edit meet (descendEdits edits index) child :: editChildren meet edits (index + 1) rest
end

mutual
  /-- Required paths remove rows with absent children before intersection. -/
  def require (paths : List Path) : Tree Tag Leaf → Tree Tag Leaf
    | .empty => .empty
    | .leaf value => if fits paths 0 then .leaf value else .empty
    | .node edges => .node (requireEdges paths edges)

  /-- Every original row must contain all required immediate child positions. -/
  def requireEdges (paths : List Path) : List (Edge Tag Leaf) → List (Edge Tag Leaf)
    | [] => []
    | .mk tag children :: rest =>
        if fits paths children.length then
          .mk tag (requireChildren paths 0 children) :: requireEdges paths rest
        else requireEdges paths rest

  /-- The same requirement trie reaches each surviving alternative. -/
  def requireChildren (paths : List Path) (index : Nat) : List (Tree Tag Leaf) → List (Tree Tag Leaf)
    | [] => []
    | child :: rest => require (descend paths index) child :: requireChildren paths (index + 1) rest
end

mutual
  /-- Every existing endpoint at a selected path is a leaf domain. -/
  def LeafAt : Path → Tree Tag Leaf → Prop
    | _, .empty => True
    | [], .leaf _ => True
    | _ :: _, .leaf _ => True
    | [], .node _ => False
    | index :: path, .node edges => LeavesAt index path edges

  /-- A path may project through several original alternatives. -/
  def LeavesAt (index : Nat) (path : Path) : List (Edge Tag Leaf) → Prop
    | [] => True
    | .mk _ children :: rest => ChildAt index path children ∧ LeavesAt index path rest

  /-- A missing child contributes no endpoint. Required-path filtering removes its row. -/
  def ChildAt : Nat → Path → List (Tree Tag Leaf) → Prop
    | _, _, [] => True
    | 0, path, child :: _ => LeafAt path child
    | index + 1, path, _ :: rest => ChildAt index path rest
end

/-- The editable paths stop before ancestor constructors in every original occurrence. -/
def Admissible (edits : List (Path × Leaf)) (tree : Tree Tag Leaf) : Prop :=
  ∀ path target, (path, target) ∈ edits → LeafAt path tree

mutual
  /-- Positive constructor weights account for deleted rows and explicit empty roots. -/
  def weight (rank : Leaf → Nat) : Tree Tag Leaf → Nat
    | .empty => 0
    | .leaf value => rank value + 1
    | .node edges => edgesWeight rank edges + 1

  /-- Each original edge contributes one positive unit in addition to its child weights. -/
  def edgesWeight (rank : Leaf → Nat) : List (Edge Tag Leaf) → Nat
    | [] => 0
    | .mk _ children :: rest => forestWeight rank children + 1 + edgesWeight rank rest

  /-- Forest weight counts occurrences even when the source has merged their identities. -/
  def forestWeight (rank : Leaf → Nat) : List (Tree Tag Leaf) → Nat
    | [] => 0
    | child :: rest => weight rank child + forestWeight rank rest
end

/-- Equal weight under progress means that every represented occurrence is unchanged. -/
def Progress (rank : α → Nat) (after before : α) : Prop :=
  rank after ≤ rank before ∧ (rank after = rank before → after = before)

/-- An unchanged occurrence always progresses. -/
theorem progress_refl (rank : α → Nat) (value : α) : Progress rank value value := ⟨Nat.le_refl _, fun _ => rfl⟩

/-- Sequential edits preserve progress and its equality test. -/
theorem progress_trans (rank : α → Nat) (before middle after : α)
    (first : Progress rank middle before) (second : Progress rank after middle) : Progress rank after before := by
  refine ⟨Nat.le_trans second.1 first.1, fun same => ?_⟩
  have leFirst := first.1
  have leSecond := second.1
  have left : rank after = rank middle := by omega
  have right : rank middle = rank before := by omega
  exact (second.2 left).trans (first.2 right)

/-- A changed occurrence strictly decreases its finite weight. -/
theorem progress_strict (rank : α → Nat) (after before : α)
    (progress : Progress rank after before) (changed : after ≠ before) : rank after < rank before := by
  have bounded := progress.1
  have different : rank after ≠ rank before := fun same => changed (progress.2 same)
  omega

end MicroCFTA.EqualityLeafProjectionSyntax
