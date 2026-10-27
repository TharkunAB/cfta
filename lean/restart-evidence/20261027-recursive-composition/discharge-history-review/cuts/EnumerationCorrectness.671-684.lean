/-- An unallocated variable is alone in its union-find class. -/
theorem outside_class (forest : UnionFind.Forest) (limit uv other : Nat) (bounded : ForestBound limit forest)
    (outside : limit ≤ uv) (same : UnionFind.SameClass forest uv other) : uv = other := by
  obtain ⟨root, count, left, right⟩ := same
  have singleton : UnionFind.Reaches forest uv uv 1 :=
    .root (by simp [UnionFind.read, outside_forest forest limit uv bounded outside])
  have equal := (UnionFind.reaches_unique left singleton).1
  subst root
  by_cases inside : other < limit
  · have impossible := reaches_bounded forest limit bounded right inside
    omega
  · have singletonOther : UnionFind.Reaches forest other other 1 :=
      .root (by simp [UnionFind.read, outside_forest forest limit other bounded (by omega)])
    exact (UnionFind.reaches_unique right singletonOther).1
