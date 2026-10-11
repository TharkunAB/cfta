import MicroCFTA.Language

/-!
# Position numbering for memoized acceptance

`Internal.Tree.acceptsBy` numbers a shared term in preorder. The cache key is
its position and graph state. This model preserves the original subtree at
each numbered node and proves that no two positions collide.
-/
namespace MicroCFTA.NumberedTerms
open Language

/-- The source's numbered tree stores the original subtree at each node. -/
inductive Positioned (Symbol : Type) where
  | node (position : Nat) (original : Term Symbol) (children : List (Positioned Symbol))

/-- Read the original subtree kept at a numbered node. -/
def original : Positioned Symbol → Term Symbol
  | .node _ term _ => term

mutual
/-- Count every constructor of a finite term. -/
def size : Term Symbol → Nat
  | .node _ children => 1 + forestSize children

/-- Count constructors in an ordered forest. -/
def forestSize : List (Term Symbol) → Nat
  | [] => 0
  | first :: rest => size first + forestSize rest
end

mutual
/-- Assign the next position before numbering the children. -/
def number (term : Term Symbol) (next : Nat) : Nat × Positioned Symbol :=
  match term with
  | .node _ children =>
    let result := numberForest children (next + 1)
    (result.1, .node next term result.2)

/-- Thread the position supply through consecutive child subtrees. -/
def numberForest : List (Term Symbol) → Nat → Nat × List (Positioned Symbol)
  | [], next => (next, [])
  | first :: rest, next =>
    let head := number first next
    let tail := numberForest rest head.1
    (tail.1, head.2 :: tail.2)
end

mutual
/-- Read the assigned positions in preorder. -/
def positions : Positioned Symbol → List Nat
  | .node position _ children => position :: forestPositions children

/-- Read every child's positions in order. -/
def forestPositions : List (Positioned Symbol) → List Nat
  | [] => []
  | first :: rest => positions first ++ forestPositions rest
end

mutual
/-- A numbered node retains the original ordered child subtrees. -/
def Valid : Positioned Symbol → Prop
  | .node _ term children =>
    (∃ symbol, term = .node symbol (children.map original)) ∧ AllValid children

/-- The same representation invariant holds at every child. -/
def AllValid : List (Positioned Symbol) → Prop
  | [] => True
  | first :: rest => Valid first ∧ AllValid rest
end

/-- Numbering preserves the original root subtree exactly. -/
theorem number_original (term : Term Symbol) (next : Nat) : original (number term next).2 = term := by
  cases term
  rfl

mutual
/-- Numbering consumes one position for each constructor. -/
theorem number_next (term : Term Symbol) (next : Nat) : (number term next).1 = next + size term := by
  cases term with
  | node symbol children => simp [number, numberForest_next, size, Nat.add_assoc]

/-- Forest numbering consumes the sum of its subtree sizes. -/
theorem numberForest_next (terms : List (Term Symbol)) (next : Nat) :
    (numberForest terms next).1 = next + forestSize terms := by
  cases terms with
  | nil => simp [numberForest, forestSize]
  | cons first rest => simp [numberForest, numberForest_next, number_next, forestSize, Nat.add_assoc]
end

/-- Reading all original children after numbering gives the exact input forest. -/
theorem numberForest_original (terms : List (Term Symbol)) (next : Nat) :
    ((numberForest terms next).2).map original = terms := by
  induction terms generalizing next with
  | nil => rfl
  | cons first rest ih => simp [numberForest, number_original, ih]

mutual
/-- Numbering establishes the complete stored-subtree invariant. -/
theorem number_valid (term : Term Symbol) (next : Nat) : Valid (number term next).2 := by
  cases term with
  | node symbol children =>
    simp only [number, Valid]
    exact ⟨⟨symbol, by rw [numberForest_original]⟩, numberForest_valid children (next + 1)⟩

/-- Every numbered child also satisfies the representation invariant. -/
theorem numberForest_valid (terms : List (Term Symbol)) (next : Nat) : AllValid (numberForest terms next).2 := by
  cases terms with
  | nil => trivial
  | cons first rest => exact ⟨number_valid first next, numberForest_valid rest (number first next).1⟩
end

mutual
/-- Numbering uses precisely one contiguous position range. -/
theorem number_positions (term : Term Symbol) (next : Nat) :
    positions (number term next).2 = List.range' next (size term) := by
  cases term with
  | node symbol children =>
    simp only [number, positions, numberForest_positions, size]
    rw [Nat.add_comm 1 (forestSize children), List.range'_succ]

/-- Numbered forests concatenate adjacent position ranges. -/
theorem numberForest_positions (terms : List (Term Symbol)) (next : Nat) :
    forestPositions (numberForest terms next).2 = List.range' next (forestSize terms) := by
  cases terms with
  | nil => rfl
  | cons first rest =>
    simp only [numberForest, forestPositions, number_positions, numberForest_positions, number_next, forestSize]
    simpa only [Nat.one_mul] using (List.range'_append (s := next) (m := size first) (n := forestSize rest) (step := 1))
end

/-- Distinct subterm positions never share a cache position. -/
theorem numbered_positions_unique (term : Term Symbol) (next : Nat) : (positions (number term next).2).Nodup := by
  rw [number_positions]
  exact List.nodup_range'

/-- Every generated position is in the allocated half-open interval. -/
theorem numbered_position_bounds (term : Term Symbol) (next position : Nat)
    (member : position ∈ positions (number term next).2) : next ≤ position ∧ position < next + size term := by
  rw [number_positions] at member
  obtain ⟨offset, bound, same⟩ := List.mem_range'.mp member
  omega

end MicroCFTA.NumberedTerms
