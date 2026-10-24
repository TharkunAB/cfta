import MicroCFTA.EnumerationPureSelection
import MicroCFTA.EnumerationSchedule

/-!
# Canonical waiting counts after actual terminal unions

The endpoint uses the observed union loop and winner lookup. The input
starts after the old representatives have been recorded. The count transfer
is complete before assimilation starts. No intermediate index invariant is
asserted between these operations.
-/
namespace MicroCFTA.EnumerationCanonicalUnion
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
    · simp [atTarget]
    · have present := (keys (roots uv)).mpr ⟨member, atTarget⟩
      simp [member, present]
  · have absent : roots uv ∉ sources := fun present => member ((keys (roots uv)).mp present).1
    simp [member, absent]

/-- The same actual union prefix realizes the completed cached-count transfer. -/
theorem terminal_transfer_correct (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (state : Cached Symbol Guard) (correct : EnumerationPureSelection.Correct graph roots state)
    (paths : Roots state.core.representatives roots) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (united after : State Symbol Guard) (target : Nat) (sources : List Nat)
    (unions : Success (rest.forM fun sc => unionVariables fuel first.var sc.var) state.core () united)
    (winner : Success (representative fuel first.var) united target after)
    (keys : ∀ key, key ∈ sources ↔ key ∈ (first :: rest).map (fun sc => roots sc.var) ∧ key ≠ target) :
    EnumerationPureSelection.Correct graph (mergedRoots roots ((first :: rest).map (fun sc => roots sc.var)) target)
      (EnumerationPureSelection.transfer target sources (EnumerationExpandableIndex.frame after state)) ∧
    Roots after.representatives (mergedRoots roots ((first :: rest).map (fun sc => roots sc.var)) target) := by
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined := terminal_unions state.core.values roots [roots first.var] fuel first.var rest state.core united
    (merging_initial state.core.values roots state.core first.var ⟨rfl, paths⟩) (by simp) unions
  obtain ⟨resolved, count, path⟩ := merging_representative state.core.values roots selected fuel first.var target
    united after joined winner
  have firstSelected : roots first.var ∈ selected :=
    (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
  have actualRoots := merging_roots state.core.values roots selected after resolved first.var target count firstSelected path
  have selectedSame (key : Nat) : key ∈ selected ↔ key ∈ (first :: rest).map (fun sc => roots sc.var) := by
    simp [selected, resolve_members]
  have counterUnited : united.counter = state.core.counter := by
    apply forM_invariant (fun sc => unionVariables fuel first.var sc.var)
      (fun current => current.counter = state.core.counter) rest _ state.core united rfl unions
    intro sc _ before next previous success
    obtain ⟨forest, _, same⟩ := (unionVariables_success fuel first.var sc.var before next).mp success
    rw [same]
    exact previous
  obtain ⟨found, _, _, finalSame⟩ := (representative_success fuel first.var united after target).mp winner
  have counterAfter : after.counter = state.core.counter := by
    rw [finalSame]
    exact counterUnited
  have framed := EnumerationPureSelection.frame_correct graph roots state after correct resolved.values counterAfter
  have transferred := EnumerationPureSelection.transfer_correct graph roots target sources
    (EnumerationExpandableIndex.frame after state) framed
  rw [redirect_fold_eq roots ((first :: rest).map (fun sc => roots sc.var)) target sources keys] at transferred
  refine ⟨transferred, ?_⟩
  intro uv
  simpa only [mergedRoots, selectedSame] using actualRoots uv

end MicroCFTA.EnumerationCanonicalUnion
