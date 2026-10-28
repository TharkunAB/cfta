open EnumerationState EnumerationSchedule EnumerationCorrectness
open EnumerationExpandableIndex (Cached)

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

/-- Replace the selected old classes by the actual winning root. -/
def mergedRoots (roots : Nat → Nat) (selected : List Nat) (target uv : Nat) : Nat :=
  if roots uv ∈ selected then target else roots uv

/-- An actual representative map fixes every representative it names. -/
theorem roots_idempotent (forest : UnionFind.Forest) (roots : Nat → Nat) (paths : Roots forest roots) :
    ∀ uv, roots (roots uv) = roots uv := by
  intro uv
  obtain ⟨size, path⟩ := paths uv
  exact (root_iff forest roots paths (roots uv)).mp ⟨size, .root (UnionFind.reaches_terminal path)⟩

/-- Actual joined classes determine the exact final root of every variable. -/
theorem merging_roots (values : List (UVarValue Symbol)) (roots : Nat → Nat) (selected : List Nat)
    (state : State Symbol Guard) (valid : Merging values roots selected state)
    (first target count : Nat) (firstSelected : roots first ∈ selected)
    (path : UnionFind.Reaches state.representatives first target count) :
    Roots state.representatives (mergedRoots roots selected target) := by
  have targetPath : UnionFind.Reaches state.representatives target target count :=
    .root (UnionFind.reaches_terminal path)
  have targetFixed : roots target = target := valid.oldRoots target ⟨count, targetPath⟩
  have targetSelected : target ∈ selected := by
    rcases (valid.joined first target).mp (UnionFind.sameClass_root path) with same | both
    · have named : roots target ∈ selected := same ▸ firstSelected
      simpa [targetFixed] using named
    · simpa [targetFixed] using both.2
  intro uv
  obtain ⟨root, size, actual⟩ := valid.total uv
  by_cases member : roots uv ∈ selected
  · have related := (valid.joined uv target).mpr
      (Or.inr ⟨member, by simpa [targetFixed] using targetSelected⟩)
    have same := (UnionFind.sameClass_iff_roots actual targetPath).mp related
    exact ⟨size, by simpa [mergedRoots, member, same] using actual⟩
  · have fixed : roots root = root :=
      valid.oldRoots root ⟨size, .root (UnionFind.reaches_terminal actual)⟩
    rcases (valid.joined uv root).mp (UnionFind.sameClass_root actual) with same | both
    · have sameRoot : root = roots uv := (same.trans fixed).symm
      exact ⟨size, by simpa [mergedRoots, member, sameRoot] using actual⟩
    · exact (member both.1).elim

private theorem redirect_fold_apply (roots : Nat → Nat) (target : Nat) (sources : List Nat) (uv : Nat) :
    (sources.foldl (fun previous source => EnumerationCanonicalWaiting.redirect target source previous) roots) uv =
      if roots uv ∈ sources then target else roots uv := by
  induction sources generalizing roots with
  | nil => rfl
  | cons source rest ih =>
      rw [List.foldl_cons, ih]
      by_cases same : roots uv = source <;> simp [EnumerationCanonicalWaiting.redirect, same]

/-- The source's deleted-winner key set gives exactly the merged root map. -/
theorem redirect_fold_eq (roots : Nat → Nat) (selected : List Nat) (target : Nat) (sources : List Nat)
    (keys : ∀ key, key ∈ sources ↔ key ∈ selected ∧ key ≠ target) :
    sources.foldl (fun previous source => EnumerationCanonicalWaiting.redirect target source previous) roots =
      mergedRoots roots selected target := by
  funext uv
  rw [redirect_fold_apply]
  unfold mergedRoots
  by_cases member : roots uv ∈ selected
  · by_cases atTarget : roots uv = target
