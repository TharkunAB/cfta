import MicroCFTA.FlatUnionFindUnion
import MicroCFTA.SourceUnionFindCompression

/-!
# Correspondence with the earlier union-find semantics

The relation retains exact representatives and sizes. It permits different
map contents and parent paths. In particular, the earlier lookup can insert
an absent singleton root while the current lookup retains its input map.
-/

namespace MicroCFTA.FlatUnionFind

/-- Every earlier path returns the direct representative and its stored size. -/
def Represents (flat : Forest) (earlier : UnionFind.Forest) : Prop :=
  ∀ uv, UnionFind.Reaches earlier uv (root flat uv) (entryOf flat (root flat uv)).1

/-- Erasing member lists gives one forest with the required path semantics. -/
theorem erase_represents (valid : Valid flat) : Represents flat (erase flat) :=
  erase_reaches valid

/-- The relation implies termination of all earlier lookups. -/
theorem represents_total (related : Represents flat earlier) : UnionFind.Total earlier :=
  fun uv => ⟨_, _, related uv⟩

/-- Both representations have exactly the same equality classes. -/
theorem represents_classes (related : Represents flat earlier) (left right : Nat) :
    UnionFind.SameClass earlier left right ↔ root flat left = root flat right :=
  UnionFind.sameClass_iff_roots (related left) (related right)

/-- Singleton initialization relates the two representations, including absent entries. -/
theorem initial_represents (variables : List Nat) :
    Represents (withInitialValues variables) (UnionFind.withInitialValues variables) := by
  intro uv
  have direct : root (withInitialValues variables) uv = uv := by
    simp [root, withInitialValues]
  have size : (entryOf (withInitialValues variables) uv).1 = 1 := by
    simp only [entryOf, withInitialValues]
    split <;> rfl
  rw [direct, size]
  exact .root (UnionFind.read_initial variables uv)

/-- A completed earlier lookup agrees on its root and size and retains the relation. -/
theorem findRoot_represents (related : Represents flat earlier)
    (completed : UnionFind.findRoot fuel earlier uv = some found) :
    found.representative = root flat uv ∧
      found.size = (entryOf flat (root flat uv)).1 ∧ Represents flat found.forest := by
  obtain ⟨path, preserved⟩ := UnionFind.findRoot_correct _ _ _ _ completed
  obtain ⟨sameRoot, sameSize⟩ := UnionFind.reaches_unique path (related uv)
  exact ⟨sameRoot, sameSize, fun other => preserved (related other)⟩

/-- The current lookup and a finite earlier execution return the same representative. -/
theorem find_refines (related : Represents flat earlier) (uv : Nat) :
    ∃ fuel found, UnionFind.findRoot fuel earlier uv = some found ∧
      found.representative = (find flat uv).1 ∧ Represents (find flat uv).2 found.forest := by
  obtain ⟨fuel, found, completed⟩ := UnionFind.findRoot_terminates (related uv)
  obtain ⟨sameRoot, _, retained⟩ := findRoot_represents related completed
  exact ⟨fuel, found, completed, sameRoot, retained⟩

private theorem link_size (valid : Valid forest)
    (loserRoot : root forest loser = loser) (winnerRoot : root forest winner = winner)
    (different : loser ≠ winner) (uv : Nat) :
    (entryOf (link forest loser winner) (root (link forest loser winner) uv)).1 =
      UnionFind.mergedSize loser winner (entryOf forest loser).1 (entryOf forest winner).1
        (root forest uv) (entryOf forest (root forest uv)).1 := by
  rw [link_root valid loserRoot winnerRoot different]
  have winnerInfo : entryOf (link forest loser winner) winner =
      ((entryOf forest winner).1 + (entryOf forest loser).1,
        (entryOf forest loser).2 ++ (entryOf forest winner).2) := by
    simp [entryOf, link, merge, put]
  by_cases isLoser : root forest uv = loser
  · simp [UnionFind.redirect, UnionFind.mergedSize, isLoser, winnerInfo, Nat.add_comm]
  · by_cases isWinner : root forest uv = winner
    · simp [UnionFind.redirect, UnionFind.mergedSize, isWinner,
        winnerInfo, Nat.add_comm]
    · have outside : root forest uv ∉ (entryOf forest loser).2 := by
        intro member
        have same := ((entryOf_spec valid loserRoot).2.2 (root forest uv)).mp member
        rw [root_root valid] at same
        exact isLoser same
      have unchanged : link forest loser winner (root forest uv) = forest (root forest uv) := by
        simp [link, merge_lookup, isWinner, outside]
      simp only [UnionFind.redirect, UnionFind.mergedSize, isLoser, isWinner,
        or_self, ↓reduceIte]
      unfold entryOf
      rw [unchanged]

/-- Merging the same two roots preserves the exact-root and exact-size relation. -/
theorem link_represents (valid : Valid flat) (related : Represents flat earlier)
    (loserRoot : root flat loser = loser) (winnerRoot : root flat winner = winner)
    (different : loser ≠ winner) :
    Represents (link flat loser winner)
      (UnionFind.link earlier loser winner (entryOf flat loser).1 (entryOf flat winner).1) := by
  have loserPath := related loser
  have winnerPath := related winner
  rw [loserRoot] at loserPath
  rw [winnerRoot] at winnerPath
  intro uv
  rw [link_size valid loserRoot winnerRoot different,
    link_root valid loserRoot winnerRoot different]
  exact UnionFind.link_reaches (UnionFind.reaches_terminal loserPath)
    (UnionFind.reaches_terminal winnerPath) different (related uv)

/-- Every successful earlier union agrees with the current root choices and class sizes. -/
theorem union_represents (valid : Valid flat) (related : Represents flat earlier)
    (completed : UnionFind.union leftFuel rightFuel earlier left right = some output) :
    Represents (union flat left right) output := by
  cases firstResult : UnionFind.findRoot leftFuel earlier left with
  | none => simp [UnionFind.union, firstResult] at completed
  | some first =>
    obtain ⟨firstRoot, firstSize, firstRelated⟩ := findRoot_represents related firstResult
    cases secondResult : UnionFind.findRoot rightFuel first.forest right with
    | none => simp [UnionFind.union, firstResult, secondResult] at completed
    | some second =>
      obtain ⟨secondRoot, secondSize, secondRelated⟩ := findRoot_represents firstRelated secondResult
      simp [UnionFind.union, firstResult, secondResult,
        firstRoot, firstSize, secondRoot, secondSize] at completed
      dsimp only [union]
      by_cases same : root flat left = root flat right
      · simp only [same, ↓reduceIte, Option.some.injEq] at completed
        subst output
        simpa only [same, ↓reduceIte] using secondRelated
      · simp only [same, ↓reduceIte, unionRoots] at completed ⊢
        split at completed
        · cases completed
          simp only [‹_ < _›, ↓reduceIte]
          exact link_represents valid secondRelated (root_root valid left)
            (root_root valid right) same
        · cases completed
          simp only [‹¬ _ < _›, ↓reduceIte]
          exact link_represents valid secondRelated (root_root valid right)
            (root_root valid left) (Ne.symm same)

/-- The current union has a corresponding finite earlier execution and remains valid. -/
theorem union_refines (valid : Valid flat) (related : Represents flat earlier)
    (left right : Nat) :
    Valid (union flat left right) ∧
      ∃ leftFuel rightFuel output,
        UnionFind.union leftFuel rightFuel earlier left right = some output ∧
          Represents (union flat left right) output := by
  obtain ⟨leftFuel, rightFuel, output, completed⟩ :=
    UnionFind.union_terminates (represents_total related) left right
  exact ⟨union_valid valid left right, leftFuel, rightFuel, output, completed,
    union_represents valid related completed⟩

/-- The conditional-compression worker has the same correspondence on successful union. -/
theorem compressed_union_represents (valid : Valid flat) (related : Represents flat earlier)
    (completed : SourceUnionFindCompression.union leftFuel rightFuel earlier left right =
      some output) : Represents (union flat left right) output := by
  rw [SourceUnionFindCompression.union_eq] at completed
  exact union_represents valid related completed

end MicroCFTA.FlatUnionFind
