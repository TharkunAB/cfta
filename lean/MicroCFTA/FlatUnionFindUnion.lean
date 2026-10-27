import MicroCFTA.FlatUnionFind

/-!
# Weighted union for direct parent pointers

The member fold can temporarily invalidate root metadata. The proofs use its
pointwise effect and establish validity after the final root write.
-/

namespace MicroCFTA.FlatUnionFind

/-- Merge two root classes with the second root as winner. -/
def link (forest : Forest) (loser winner : Nat) : Forest :=
  merge forest winner (entryOf forest winner).1 (entryOf forest loser).1
    (entryOf forest loser).2 (entryOf forest winner).2

private theorem link_lookup (forest : Forest) (loser winner uv : Nat) :
    link forest loser winner uv =
      if uv = winner then
        some (.root ((entryOf forest winner).1 + (entryOf forest loser).1)
          ((entryOf forest loser).2 ++ (entryOf forest winner).2))
      else if uv ∈ (entryOf forest loser).2 then some (.parent winner) else forest uv := by
  exact merge_lookup ..

/-- A complete merge redirects exactly the losing class. -/
theorem link_root (valid : Valid forest)
    (loserRoot : root forest loser = loser) (winnerRoot : root forest winner = winner)
    (different : loser ≠ winner) (uv : Nat) :
    root (link forest loser winner) uv =
      UnionFind.redirect loser winner (root forest uv) := by
  have member := (entryOf_spec valid loserRoot).2.2 uv
  by_cases isWinner : uv = winner
  · subst uv
    rw [winnerRoot]
    simp [root, link_lookup, UnionFind.redirect, Ne.symm different]
  · by_cases inLoser : uv ∈ (entryOf forest loser).2
    · rw [member.mp inLoser]
      simp [root, link_lookup, isWinner, inLoser, UnionFind.redirect]
    · have unchanged : link forest loser winner uv = forest uv := by
        simp [link_lookup, isWinner, inLoser]
      have notLoser : root forest uv ≠ loser := fun same => inLoser (member.mpr same)
      simp only [UnionFind.redirect, notLoser, ↓reduceIte]
      unfold root
      rw [unchanged]

/-- The complete merge preserves direct parents and exact finite class metadata. -/
theorem link_valid (valid : Valid forest)
    (loserRoot : root forest loser = loser) (winnerRoot : root forest winner = winner)
    (different : loser ≠ winner) : Valid (link forest loser winner) := by
  obtain ⟨loserNodup, loserSize, loserMembers⟩ := entryOf_spec valid loserRoot
  obtain ⟨winnerNodup, winnerSize, winnerMembers⟩ := entryOf_spec valid winnerRoot
  have roots := link_root valid loserRoot winnerRoot different
  have winnerLookup := link_lookup forest loser winner winner
  simp only [↓reduceIte] at winnerLookup
  refine ⟨?_, ?_⟩
  · intro uv parent lookup
    by_cases isWinner : uv = winner
    · subst uv
      rw [winnerLookup] at lookup
      cases lookup
    · by_cases inLoser : uv ∈ (entryOf forest loser).2
      · simp only [link_lookup, isWinner, ↓reduceIte, inLoser] at lookup
        cases lookup
        exact ⟨_, _, winnerLookup⟩
      · have original : forest uv = some (.parent parent) := by
          simpa only [link_lookup, isWinner, ↓reduceIte, inLoser] using lookup
        obtain ⟨size, members, terminal⟩ := valid.parents uv parent original
        have parentFixed : root forest parent = parent := by simp [root, terminal]
        have parentNotLoser : parent ≠ loser := by
          intro same
          apply inLoser
          apply (loserMembers uv).mpr
          simp [root, original, same]
        by_cases parentWinner : parent = winner
        · subst parent
          exact ⟨_, _, winnerLookup⟩
        · have parentOutside : parent ∉ (entryOf forest loser).2 := by
            intro member
            exact parentNotLoser (parentFixed.symm.trans ((loserMembers parent).mp member))
          exact ⟨size, members, by simp [link_lookup, parentWinner, parentOutside, terminal]⟩
  · intro representative size members lookup
    by_cases isWinner : representative = winner
    · subst representative
      rw [winnerLookup] at lookup
      cases lookup
      refine ⟨List.nodup_append.mpr ⟨loserNodup, winnerNodup, ?_⟩, ?_, ?_⟩
      · intro left inLeft right inRight same
        have leftRoot := (loserMembers left).mp inLeft
        have rightRoot := (winnerMembers right).mp inRight
        exact different (leftRoot.symm.trans (same ▸ rightRoot))
      · simp only [List.length_append, loserSize, winnerSize]
        omega
      · intro uv
        rw [List.mem_append, roots]
        simp only [loserMembers, winnerMembers, UnionFind.redirect]
        by_cases isLoser : root forest uv = loser <;> simp [isLoser]
    · have outside : representative ∉ (entryOf forest loser).2 := by
        intro member
        simp [link_lookup, isWinner, member] at lookup
      have original : forest representative = some (.root size members) := by
        simpa only [link_lookup, isWinner, ↓reduceIte, outside] using lookup
      obtain ⟨nodup, count, originalMembers⟩ := valid.roots representative size members original
      have representativeNotLoser : representative ≠ loser := by
        intro same
        apply outside
        apply (loserMembers representative).mpr
        simpa only [same] using loserRoot
      refine ⟨nodup, count, ?_⟩
      intro uv
      rw [originalMembers, roots]
      simp only [UnionFind.redirect]
      by_cases isLoser : root forest uv = loser
      · simp [isLoser, Ne.symm isWinner, Ne.symm representativeNotLoser]
      · simp [isLoser]

/-- Merge distinct roots and select the larger class. Ties select the first root. -/
def unionRoots (forest : Forest) (left right : Nat) : Nat × Forest :=
  if (entryOf forest left).1 < (entryOf forest right).1 then
    (right, link forest left right)
  else (left, link forest right left)

/-- Merge two variable classes after their direct root reads. -/
def union (forest : Forest) (left right : Nat) : Forest :=
  let leftRoot := root forest left
  let rightRoot := root forest right
  if leftRoot = rightRoot then forest else (unionRoots forest leftRoot rightRoot).2

/-- Weighted union of distinct roots preserves the representation invariant. -/
theorem unionRoots_valid (valid : Valid forest)
    (leftRoot : root forest left = left) (rightRoot : root forest right = right)
    (different : left ≠ right) : Valid (unionRoots forest left right).2 := by
  unfold unionRoots
  split
  · exact link_valid valid leftRoot rightRoot different
  · exact link_valid valid rightRoot leftRoot (Ne.symm different)

/-- Union preserves the representation invariant for every pair of variables. -/
theorem union_valid (valid : Valid forest) (left right : Nat) :
    Valid (union forest left right) := by
  dsimp only [union]
  split
  · exact valid
  · exact unionRoots_valid valid (root_root valid left) (root_root valid right) ‹_›

end MicroCFTA.FlatUnionFind
