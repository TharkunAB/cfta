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
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (inside : held < before.counter) (root : IsRoot before.representatives held)
    (incoming : IncomingAvoid held before) (inputs : Avoids before.representatives held scs)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (success : Success (enumerateNode graph fuel scs node) before fragment after) : IncomingAvoid held after := by
  have allowed := (enumeration_allowed (fun uv => ¬UnionFind.SameClass before.representatives held uv) before.counter
    (fresh_separate before safe held inside) graph fuel).1 scs node before after fragment safe (Nat.le_refl _) incoming inputs bounded success
  have frame := (enumeration_protected graph fuel).1 scs node held before after fragment safe inside root bounded inputs success
  intro value member sc listed same
  exact allowed value member sc listed ((frame.classes sc.var).mp same)

/-- Every stored suspended reference avoids all expanded slots. -/
def PendingReferences (state : State Symbol Guard) : Prop :=
  ∀ held fragment, state.values[held]? = some (.enumerated fragment) → IncomingAvoid held state
