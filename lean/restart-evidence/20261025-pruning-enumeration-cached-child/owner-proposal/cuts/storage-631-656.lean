def SlotBound (limit : Nat) : UVarValue Symbol → Prop
  | .unenumerated _ scs => ∀ sc ∈ scs, sc.var < limit
  | .enumerated fragment => FragmentBound limit fragment
  | .eliminated => True

/-- Every stored union-find address and parent target stays inside the allocation domain. -/
def ForestBound (limit : Nat) (forest : UnionFind.Forest) : Prop :=
  ∀ uv entry, forest uv = some entry → uv < limit ∧
    match entry with
    | .root _ => True
    | .parent next => next < limit

/-- Storage safety needed to justify fresh-variable extension and representative lookup. -/
structure StorageValid (state : State Symbol Guard) : Prop where
  aligned : SupplyAligned state
  total : UnionFind.Total state.representatives
  forest : ForestBound state.counter state.representatives
  values : ∀ value ∈ state.values, SlotBound state.counter value
  guards : ∀ obligation ∈ state.obligations, FragmentBound state.counter obligation.2

/-- No unallocated variable has an explicit union-find entry. -/
theorem outside_forest (forest : UnionFind.Forest) (limit uv : Nat) (bounded : ForestBound limit forest)
    (outside : limit ≤ uv) : forest uv = none := by
  cases entry : forest uv with
  | none => rfl
  | some value => have below := (bounded uv value entry).1; omega
