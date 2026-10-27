inductive Entry where
  | parent (uv : Nat)
  | root (size : Nat)
deriving DecidableEq, Repr

/-- A persistent finite-map interface. Missing variables are allowed. -/
abbrev Forest := Nat → Option Entry

/-- A missing variable denotes a singleton root. -/
def read (forest : Forest) (uv : Nat) : Entry :=
  (forest uv).getD (.root 1)

/-- Replace one entry and retain every other entry. -/
def put (forest : Forest) (uv : Nat) (entry : Entry) : Forest :=
  fun other => if other = uv then some entry else forest other

@[simp] theorem read_put_same (forest : Forest) (uv : Nat) (entry : Entry) :
    read (put forest uv entry) uv = entry := by simp [read, put]

@[simp] theorem read_put_other (forest : Forest) (uv other : Nat) (entry : Entry)
    (different : other ≠ uv) : read (put forest uv entry) other = read forest other := by
  simp [read, put, different]

/-- A finite parent path ends at a root and returns its stored size. -/
inductive Reaches (forest : Forest) : Nat → Nat → Nat → Prop where
  | root (lookup : read forest uv = .root size) : Reaches forest uv uv size
  | parent (lookup : read forest uv = .parent next)
      (tail : Reaches forest next representative size) : Reaches forest uv representative size

/-- A path's final variable is a root. -/
theorem reaches_terminal (path : Reaches forest uv representative size) :
    read forest representative = .root size := by
  induction path with
  | root lookup => exact lookup
  | parent _ _ ih => exact ih

/-- A finite parent path has a unique representative and stored size. -/
theorem reaches_unique (left : Reaches forest uv root₁ size₁)
    (right : Reaches forest uv root₂ size₂) : root₁ = root₂ ∧ size₁ = size₂ := by
  induction left generalizing root₂ size₂ with
  | root lookup =>
    cases right with
    | root other => simp_all
    | parent other tail => simp_all
  | parent lookup tail ih =>
