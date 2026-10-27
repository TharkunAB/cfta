        subst after
        exact guardedValid

/-- Every stored reference avoids one protected root class. -/
def IncomingAvoid (held : Nat) (state : State Symbol Guard) : Prop :=
  ReferencesAllowed (fun uv => ¬UnionFind.SameClass state.representatives held uv) state

/-- All fresh variables avoid an allocated old class. -/
theorem fresh_separate (state : State Symbol Guard) (safe : Safe state) (held : Nat) (inside : held < state.counter) :
    ∀ uv, state.counter ≤ uv → ¬UnionFind.SameClass state.representatives held uv := by
  intro uv outside same
  have equal := outside_class state.representatives state.counter uv held safe.1.forest outside (UnionFind.sameClass_symm same)
  omega

/-- Actual node traversal retains the absence of incoming references to its protected root. -/
theorem enumerateNode_incoming (graph : Graph Symbol Guard) (fuel node held : Nat) (scs : List Suspended)
