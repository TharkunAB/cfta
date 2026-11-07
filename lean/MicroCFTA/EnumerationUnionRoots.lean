import MicroCFTA.FlatUnionFindUnion
import MicroCFTA.EnumerationCanonicalWaiting

/-!
# Root maps for the enumeration union fold

The fold keeps the original head variable as its first union argument.
The resulting root map redirects exactly the classes named before the fold.
The redirect list can use any order and can contain repeated entries.
Machine integer representation is outside these statements.
-/

namespace MicroCFTA.EnumerationUnionRoots

open FlatUnionFind

/-- Execute the source fold of unions against the original head variable. -/
def mergeClasses (forest : Forest) (head : Nat) (tail : List Nat) : Forest :=
  tail.foldl (fun current source => union current head source) forest

/-- Appending one source executes one more union on the returned forest. -/
theorem mergeClasses_snoc (forest : Forest) (head : Nat) (tail : List Nat) (source : Nat) :
    mergeClasses forest head (tail ++ [source]) = union (mergeClasses forest head tail) head source := by
  simp [mergeClasses, List.foldl_append]

/-- Every completed union in the fold preserves the direct-parent invariant. -/
theorem mergeClasses_valid (forest : Forest) (head : Nat) (tail : List Nat) (valid : Valid forest) :
    Valid (mergeClasses forest head tail) := by
  induction tail generalizing forest with
  | nil => exact valid
  | cons source rest ih =>
      exact ih (union forest head source) (union_valid valid head source)

private theorem union_spec (forest : Forest) (valid : Valid forest) (head source : Nat) :
    ∃ winner, (winner = root forest head ∨ winner = root forest source) ∧
      ∀ query, root (union forest head source) query =
        if root forest query = root forest head ∨ root forest query = root forest source
        then winner else root forest query := by
  dsimp only [union]
  split
  · rename_i same
    refine ⟨root forest head, Or.inl rfl, ?_⟩
    intro query
    by_cases selected : root forest query = root forest head <;> simp_all
  · rename_i different
    dsimp only [unionRoots]
    split
    · refine ⟨root forest source, Or.inr rfl, ?_⟩
      intro query
      rw [link_root valid (root_root valid head) (root_root valid source) different]
      by_cases first : root forest query = root forest head <;>
        by_cases second : root forest query = root forest source <;>
        simp_all [UnionFind.redirect]
    · refine ⟨root forest head, Or.inl rfl, ?_⟩
      intro query
      rw [link_root valid (root_root valid source) (root_root valid head) (Ne.symm different)]
      by_cases first : root forest query = root forest head <;>
        by_cases second : root forest query = root forest source <;>
        simp_all [UnionFind.redirect]

private theorem mergeClasses_spec (forest : Forest) (head : Nat) (tail : List Nat) (valid : Valid forest) :
    root (mergeClasses forest head tail) head ∈ (head :: tail).map (root forest) ∧
      ∀ query, root (mergeClasses forest head tail) query =
        if root forest query ∈ (head :: tail).map (root forest)
        then root (mergeClasses forest head tail) head else root forest query := by
  suffices reversed : ∀ reversed : List Nat,
      root (mergeClasses forest head reversed.reverse) head ∈
          (head :: reversed.reverse).map (root forest) ∧
        ∀ query, root (mergeClasses forest head reversed.reverse) query =
          if root forest query ∈ (head :: reversed.reverse).map (root forest)
          then root (mergeClasses forest head reversed.reverse) head else root forest query by
    simpa only [List.reverse_reverse] using reversed tail.reverse
  intro reversed
  induction reversed with
  | nil =>
      refine ⟨by simp [mergeClasses], ?_⟩
      intro query
      by_cases same : root forest query = root forest head <;> simp [mergeClasses, same]
  | cons source reversed ih =>
      simp only [List.reverse_cons]
      let earlierTail := reversed.reverse
      let previous := mergeClasses forest head earlierTail
      let oldRoots := (head :: earlierTail).map (root forest)
      let previousTarget := root previous head
      have targetMember : previousTarget ∈ oldRoots := ih.1
      have previousRoots : ∀ query, root previous query =
          if root forest query ∈ oldRoots then previousTarget else root forest query := ih.2
      obtain ⟨winner, chosen, step⟩ := union_spec previous
        (mergeClasses_valid forest head earlierTail valid) head source
      have headStep : root (union previous head source) head = winner := by
        rw [step]
        simp
      have appendedRoots : (head :: (earlierTail ++ [source])).map (root forest) =
          oldRoots ++ [root forest source] := by
        simp [oldRoots]
      change root (mergeClasses forest head (earlierTail ++ [source])) head ∈
          (head :: (earlierTail ++ [source])).map (root forest) ∧
        ∀ query, root (mergeClasses forest head (earlierTail ++ [source])) query =
          if root forest query ∈ (head :: (earlierTail ++ [source])).map (root forest)
          then root (mergeClasses forest head (earlierTail ++ [source])) head else root forest query
      rw [mergeClasses_snoc, appendedRoots, headStep]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton]
        rcases chosen with fromHead | fromSource
        · left
          simpa only [fromHead] using targetMember
        · rw [fromSource, previousRoots]
          by_cases sourceMember : root forest source ∈ oldRoots
          · left
            simpa [sourceMember] using targetMember
          · right
            simp [sourceMember]
      · intro query
        rw [step]
        change (if root previous query = previousTarget ∨ root previous query = root previous source
            then winner else root previous query) =
          if root forest query ∈ oldRoots ++ [root forest source] then winner else root forest query
        by_cases queryMember : root forest query ∈ oldRoots
        · have queryPrevious : root previous query = previousTarget := by
            simpa [queryMember] using previousRoots query
          simp [queryPrevious, queryMember]
        · have queryPrevious : root previous query = root forest query := by
            simpa [queryMember] using previousRoots query
          have notTarget : root forest query ≠ previousTarget := by
            intro same
            apply queryMember
            simpa [same] using targetMember
          by_cases sourceMember : root forest source ∈ oldRoots
          · have sourcePrevious : root previous source = previousTarget := by
              simpa [sourceMember] using previousRoots source
            have notSource : root forest query ≠ root forest source := by
              intro same
              apply queryMember
              simpa [same] using sourceMember
            simp [queryPrevious, sourcePrevious, queryMember, notTarget, notSource]
          · have sourcePrevious : root previous source = root forest source := by
              simpa [sourceMember] using previousRoots source
            simp [queryPrevious, sourcePrevious, queryMember, notTarget]

/-- The final representative is one of the roots named before the unions. -/
theorem mergeClasses_target_mem (forest : Forest) (head : Nat) (tail : List Nat) (valid : Valid forest) :
    root (mergeClasses forest head tail) head ∈ (head :: tail).map (root forest) :=
  (mergeClasses_spec forest head tail valid).1

/-- The fold changes exactly the original classes of the supplied variables. -/
theorem mergeClasses_root (forest : Forest) (head : Nat) (tail : List Nat)
    (valid : Valid forest) (query : Nat) :
    root (mergeClasses forest head tail) query =
      if root forest query ∈ (head :: tail).map (root forest)
      then root (mergeClasses forest head tail) head else root forest query :=
  (mergeClasses_spec forest head tail valid).2 query

/-- List the distinct old roots that must transfer their counts to the final root. -/
def mergeSources (forest : Forest) (head : Nat) (tail : List Nat) : List Nat :=
  (((head :: tail).map (root forest)).eraseDups).filter
    (fun source => source != root (mergeClasses forest head tail) head)

/-- Transfer sources are exactly the old roots other than the final target. -/
theorem mem_mergeSources (forest : Forest) (head : Nat) (tail : List Nat) (source : Nat) :
    source ∈ mergeSources forest head tail ↔
      source ∈ (head :: tail).map (root forest) ∧
        source ≠ root (mergeClasses forest head tail) head := by
  simp [mergeSources]

/-- The canonical transfer list contains each old root at most once. -/
private theorem eraseDups_nodup (values : List Nat) : values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      exact ⟨by simp, eraseDups_nodup _⟩
termination_by values.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The canonical transfer list contains each old root at most once. -/
theorem mergeSources_nodup (forest : Forest) (head : Nat) (tail : List Nat) :
    (mergeSources forest head tail).Nodup := by
  exact List.Pairwise.filter _ (eraseDups_nodup _)

/-- A redirect fold depends only on source membership, not order or repetition. -/
theorem redirect_fold_apply (target : Nat) (sources : List Nat) (roots : Nat → Nat) (query : Nat) :
    (sources.foldl (fun current source => EnumerationCanonicalWaiting.redirect target source current)
      roots) query = if roots query ∈ sources then target else roots query := by
  induction sources generalizing roots with
  | nil => simp
  | cons source rest ih =>
      simp only [List.foldl_cons, ih, EnumerationCanonicalWaiting.redirect, List.mem_cons]
      by_cases same : roots query = source <;> simp [same]

/-- Any two transfer lists with the same membership give the same root map. -/
theorem redirect_fold_congr (target : Nat) (roots : Nat → Nat) (first second : List Nat)
    (same : ∀ source, source ∈ first ↔ source ∈ second) :
    first.foldl (fun current source => EnumerationCanonicalWaiting.redirect target source current) roots =
      second.foldl (fun current source => EnumerationCanonicalWaiting.redirect target source current) roots := by
  funext query
  simp only [redirect_fold_apply, same]

/-- The actual union fold supplies the canonical count-transfer root map. -/
theorem mergeClasses_root_redirect (forest : Forest) (head : Nat) (tail : List Nat) (valid : Valid forest) :
    root (mergeClasses forest head tail) =
      (mergeSources forest head tail).foldl
        (fun current source => EnumerationCanonicalWaiting.redirect
          (root (mergeClasses forest head tail) head) source current) (root forest) := by
  funext query
  rw [mergeClasses_root forest head tail valid query, redirect_fold_apply]
  by_cases isTarget : root forest query = root (mergeClasses forest head tail) head
  · simp [isTarget]
  · simp [mem_mergeSources, isTarget]

/-- An ascending set view or any other equal-membership list gives the same map. -/
theorem mergeClasses_root_redirect_of_membership (forest : Forest) (head : Nat) (tail : List Nat)
    (valid : Valid forest) (sources : List Nat)
    (same : ∀ source, source ∈ sources ↔ source ∈ mergeSources forest head tail) :
    root (mergeClasses forest head tail) =
      sources.foldl (fun current source => EnumerationCanonicalWaiting.redirect
        (root (mergeClasses forest head tail) head) source current) (root forest) := by
  exact (mergeClasses_root_redirect forest head tail valid).trans
    (redirect_fold_congr (root (mergeClasses forest head tail) head) (root forest)
      (mergeSources forest head tail) sources (fun source => (same source).symm))

end MicroCFTA.EnumerationUnionRoots
