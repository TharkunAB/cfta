/-- The selected canonical representative of every variable has a finite path. -/
def Roots (forest : UnionFind.Forest) (roots : Nat → Nat) : Prop :=
  ∀ uv, ∃ size, UnionFind.Reaches forest uv (roots uv) size
