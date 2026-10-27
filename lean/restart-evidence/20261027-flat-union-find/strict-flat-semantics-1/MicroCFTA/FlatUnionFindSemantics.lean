import MicroCFTA.FlatUnionFindRefinement

/-!
# Equality semantics of the current union-find backend

Union adds exactly one requested equality. Finite union histories retain the
representation invariant and have corresponding earlier bounded executions.
-/

namespace MicroCFTA.FlatUnionFind

/-- An assignment gives equal values to variables with the same direct root. -/
def Satisfies (forest : Forest) (assignment : Nat → α) : Prop :=
  ∀ left right, root forest left = root forest right → assignment left = assignment right

/-- The two representations permit exactly the same assignments. -/
theorem represents_satisfies (related : Represents flat earlier) (assignment : Nat → α) :
    UnionFind.Satisfies earlier assignment ↔ Satisfies flat assignment := by
  simp only [UnionFind.Satisfies, Satisfies, represents_classes related]

/-- Current union merges exactly the requested classes. -/
theorem union_classes (valid : Valid forest) (left right x y : Nat) :
    root (union forest left right) x = root (union forest left right) y ↔
      root forest x = root forest y ∨
      (root forest x = root forest left ∧ root forest y = root forest right) ∨
      (root forest x = root forest right ∧ root forest y = root forest left) := by
  have related := erase_represents valid
  obtain ⟨_, leftFuel, rightFuel, output, completed, after⟩ := union_refines valid related left right
  simpa only [represents_classes after, represents_classes related] using
    (UnionFind.union_correct (represents_total related) completed).2 x y

/-- Current union adds exactly the requested value equality. -/
theorem union_satisfies (valid : Valid forest) (left right : Nat) (assignment : Nat → α) :
    Satisfies (union forest left right) assignment ↔
      Satisfies forest assignment ∧ assignment left = assignment right := by
  have related := erase_represents valid
  obtain ⟨_, leftFuel, rightFuel, output, completed, after⟩ := union_refines valid related left right
  simpa only [represents_satisfies after, represents_satisfies related] using
    UnionFind.union_satisfies (represents_total related) completed assignment

/-- Execute the requested unions in list order. -/
def unions (forest : Forest) (requests : List (Nat × Nat)) : Forest :=
  requests.foldl (fun current request => union current request.1 request.2) forest

/-- A finite ordered history of successful earlier union calls. -/
inductive EarlierUnions : UnionFind.Forest → List (Nat × Nat) → UnionFind.Forest → Prop where
  /-- An empty request list retains the forest. -/
  | nil : EarlierUnions forest [] forest
  /-- The first call succeeds with finite bounds before the remaining calls. -/
  | cons (completed : UnionFind.union leftFuel rightFuel forest left right = some next)
      (tail : EarlierUnions next rest output) :
      EarlierUnions forest ((left, right) :: rest) output

/-- Every finite current union history preserves validity and has an exact-root counterpart. -/
theorem unions_refine (valid : Valid flat) (related : Represents flat earlier)
    (requests : List (Nat × Nat)) :
    Valid (unions flat requests) ∧
      ∃ output, EarlierUnions earlier requests output ∧ Represents (unions flat requests) output := by
  induction requests generalizing flat earlier with
  | nil => exact ⟨valid, earlier, .nil, related⟩
  | cons request rest ih =>
    obtain ⟨nextValid, leftFuel, rightFuel, next, completed, nextRelated⟩ :=
      union_refines valid related request.1 request.2
    obtain ⟨finalValid, output, trace, finalRelated⟩ := ih nextValid nextRelated
    exact ⟨finalValid, output, .cons completed trace, finalRelated⟩

/-- Initialization and every finite union history satisfy the current representation invariant. -/
theorem initialized_unions_valid (variables : List Nat) (requests : List (Nat × Nat)) :
    Valid (unions (withInitialValues variables) requests) :=
  (unions_refine (initial_valid variables) (initial_represents variables) requests).1

end MicroCFTA.FlatUnionFind
