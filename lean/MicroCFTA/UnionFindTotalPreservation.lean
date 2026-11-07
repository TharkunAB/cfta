import MicroCFTA.UnionFindSupport

namespace MicroCFTA.UnionFindTotalPreservation

open UnionFind UnionFindSupport

/-- Linking preserves termination because the winner becomes a root. -/
theorem link_preserves_total (forest : Forest) (total : Total forest)
    (loser winner loserSize winnerSize : Nat) :
    Total (link forest loser winner loserSize winnerSize) := by
  have winnerRoot : MicroCFTA.UnionFind.read
      (link forest loser winner loserSize winnerSize) winner =
      .root (loserSize + winnerSize) := by
    simp [MicroCFTA.UnionFind.read, link, put]
  have loserParent (different : loser ≠ winner) :
      MicroCFTA.UnionFind.read (link forest loser winner loserSize winnerSize) loser =
      .parent winner := by
    simp [MicroCFTA.UnionFind.read, link, put, different]
  have unchanged (key : Nat) (notLoser : key ≠ loser) (notWinner : key ≠ winner) :
      MicroCFTA.UnionFind.read (link forest loser winner loserSize winnerSize) key =
      MicroCFTA.UnionFind.read forest key := by
    simp [MicroCFTA.UnionFind.read, link, put, notLoser, notWinner]
  intro key
  obtain ⟨root, size, path⟩ := total key
  obtain ⟨depth, counted⟩ := reaches_has_parentDepth path
  clear path root size
  induction counted with
  | root key size lookup =>
    by_cases hitWinner : key = winner
    · subst key
      exact ⟨winner, loserSize + winnerSize, Reaches.root winnerRoot⟩
    by_cases hitLoser : key = loser
    · subst key
      exact ⟨winner, loserSize + winnerSize,
        Reaches.parent (loserParent hitWinner) (Reaches.root winnerRoot)⟩
    · exact ⟨key, size, Reaches.root (by rw [unchanged key hitLoser hitWinner]; exact lookup)⟩
  | step key next depth lookup tail ih =>
    by_cases hitWinner : key = winner
    · subst key
      exact ⟨winner, loserSize + winnerSize, Reaches.root winnerRoot⟩
    by_cases hitLoser : key = loser
    · subst key
      exact ⟨winner, loserSize + winnerSize,
        Reaches.parent (loserParent hitWinner) (Reaches.root winnerRoot)⟩
    · obtain ⟨root, size, route⟩ := ih
      exact ⟨root, size, Reaches.parent
        (by rw [unchanged key hitLoser hitWinner]; exact lookup) route⟩

/-- A successful union preserves termination of all representative searches. -/
theorem union_preserves_total (forest after : Forest)
    (leftFuel rightFuel left right : Nat)
    (total : Total forest)
    (run : union leftFuel rightFuel forest left right = some after) :
    Total after := by
  cases firstRun : findRoot leftFuel forest left with
  | none => simp [union, firstRun] at run
  | some first =>
    have firstTotal : Total first.forest := UnionFind.findRoot_total total firstRun
    cases secondRun : findRoot rightFuel first.forest right with
    | none => simp [union, firstRun, secondRun] at run
    | some second =>
      have secondTotal : Total second.forest := UnionFind.findRoot_total firstTotal secondRun
      by_cases same : first.representative = second.representative
      · have returned : second.forest = after := by
          simpa [union, firstRun, secondRun, same] using run
        rw [← returned]
        exact secondTotal
      · by_cases smaller : first.size < second.size
        · have returned : link second.forest first.representative second.representative
              first.size second.size = after := by
            simpa [union, firstRun, secondRun, same, smaller] using run
          rw [← returned]
          exact link_preserves_total _ secondTotal _ _ _ _
        · have returned : link second.forest second.representative first.representative
              second.size first.size = after := by
            simpa [union, firstRun, secondRun, same, smaller] using run
          rw [← returned]
          exact link_preserves_total _ secondTotal _ _ _ _

/-- Bounded queries share one fuel and preserve all forest invariants. -/
theorem union_bounded_uniformFuel (bound : Nat) (forest : Forest) (left right : Nat)
    (supported : SupportedBelow bound forest) (parents : ParentsBelow bound forest)
    (total : Total forest) (leftBelow : left < bound) (rightBelow : right < bound) :
    ∃ after, union (bound + 1) (bound + 1) forest left right = some after ∧
      SupportedBelow bound after ∧ ParentsBelow bound after ∧ Total after := by
  have grownEq : max bound (max (left + 1) (right + 1)) = bound := by omega
  have witness := UnionFindSupport.union_uniformFuel bound forest left right
    supported parents total
  dsimp only at witness
  rw [grownEq] at witness
  obtain ⟨after, run, nextSupport, nextParents⟩ := witness
  exact ⟨after, run, nextSupport, nextParents,
    union_preserves_total forest after (bound + 1) (bound + 1) left right total run⟩

end MicroCFTA.UnionFindTotalPreservation
