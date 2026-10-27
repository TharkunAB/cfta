
/-- Compression changes only the forest and preserves exact root paths. -/
structure Frame (before after : State Symbol Guard) : Prop where
  /-- Compression keeps the allocation counter. -/
  counter : after.counter = before.counter
  /-- Compression keeps every stored slot. -/
  values : after.values = before.values
  /-- Compression keeps every residual obligation. -/
  obligations : after.obligations = before.obligations
  /-- Compression keeps the complete per-variable ancestry function. -/
  recursionAncestry : after.recursionAncestry = before.recursionAncestry
  /-- Compression keeps the current expansion ancestry. -/
  expansionAncestry : after.expansionAncestry = before.expansionAncestry
  /-- Every finite root path has the same representative and size. -/
  reaches : ∀ uv root size,
    UnionFind.Reaches after.representatives uv root size ↔
      UnionFind.Reaches before.representatives uv root size

/-- An unchanged state satisfies the complete frame. -/
theorem Frame.refl (state : State Symbol Guard) : Frame state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => Iff.rfl⟩

/-- Consecutive frames preserve the same fields and root paths. -/
theorem Frame.trans (left : Frame before middle) (right : Frame middle after) : Frame before after :=
  ⟨right.counter.trans left.counter, right.values.trans left.values,
    right.obligations.trans left.obligations, right.recursionAncestry.trans left.recursionAncestry,
    right.expansionAncestry.trans left.expansionAncestry,
    fun uv root size => (right.reaches uv root size).trans (left.reaches uv root size)⟩

/-- A complete frame preserves finite root paths for every variable. -/
theorem Frame.total (frame : Frame before after) (total : UnionFind.Total before.representatives) :
    UnionFind.Total after.representatives := by
  intro uv
  obtain ⟨root, size, path⟩ := total uv
  exact ⟨root, size, (frame.reaches uv root size).mpr path⟩

/-- A pure result changes no state field. -/
theorem pure_frame (value result : α) (before after : State Symbol Guard)
    (success : Success (pure value) before result after) : Frame before after := by
  obtain ⟨_, same⟩ := (success_pure value result before after).mp success
  subst after
  exact .refl before

/-- Reading the complete state changes no field. -/
theorem get_frame (before after value : State Symbol Guard)
    (success : Success get before value after) : Frame before after := by
  obtain ⟨_, same⟩ := (get_success before after value).mp success
  subst after
  exact .refl before

/-- The actual representative read preserves root identities and stored sizes. -/
theorem representative_frame (fuel uv root : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives)
    (success : Success (representative fuel uv) before root after) : Frame before after := by
  obtain ⟨found, lookup, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro other actual size
  exact UnionFind.findRoot_reaches_iff total lookup other actual size

/-- A successful value read retains the actual root, its size, and its slot. -/
theorem getValue_frame (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (total : UnionFind.Total before.representatives)
    (success : Success (getValue fuel uv) before value after) :
    Frame before after ∧ ∃ root size,
      UnionFind.Reaches before.representatives uv root size ∧
      UnionFind.Reaches after.representatives uv root size ∧ before.values[root]? = some value := by
  obtain ⟨found, lookup, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  obtain ⟨path, preserved⟩ := UnionFind.findRoot_correct fuel before.representatives uv found lookup
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, found.representative, found.size, path, preserved path, stored⟩
  intro other root size
  exact UnionFind.findRoot_reaches_iff total lookup other root size

/-- Resolving one suspended reference preserves the complete frame. -/
private theorem resolve_frame (fuel : Nat) (blocked result : List Nat) (sc : Suspended)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (resolve fuel blocked sc) before result after) : Frame before after := by
  unfold resolve at success
  obtain ⟨root, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
  exact (representative_frame fuel sc.var root before middle total reading).trans
    (pure_frame (root :: blocked) result middle after final)

/-- Scanning one value preserves every field outside the forest. -/
