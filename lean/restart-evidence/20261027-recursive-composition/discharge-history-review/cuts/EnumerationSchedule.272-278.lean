/-- A live slot holds a value exactly when its index is a representative. -/
def IsRoot (forest : UnionFind.Forest) (uv : Nat) : Prop :=
  ∃ size, UnionFind.Reaches forest uv uv size

/-- Every allocated nonrepresentative is eliminated; every allocated representative is live. -/
def LiveRoots (state : State Symbol Guard) : Prop :=
  ∀ uv value, state.values[uv]? = some value → (value ≠ .eliminated ↔ IsRoot state.representatives uv)
