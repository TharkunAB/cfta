theorem getValue_root (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (safe : Safe before) (inside : uv < before.counter) (root : IsRoot before.representatives uv)
    (success : Success (getValue fuel uv) before value after) :
    Safe after ∧ after.counter = before.counter ∧ Protected uv before after ∧
      after.values[uv]? = some value := by
  obtain ⟨found, lookup, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  have fixed : found.representative = uv :=
    (UnionFind.reaches_unique (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1 root.choose_spec).1
  obtain ⟨safeAfter, frame⟩ := compression_safe before safe fuel uv uv inside root found lookup
  exact ⟨safeAfter, rfl, frame, by simpa [fixed] using stored⟩
