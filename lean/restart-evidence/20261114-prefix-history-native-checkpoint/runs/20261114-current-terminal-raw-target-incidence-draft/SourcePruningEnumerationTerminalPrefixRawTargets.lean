import MicroCFTA.SourcePruningEnumerationEntryRecordedBucketOrigin
import MicroCFTA.SourcePruningEnumerationTerminalPrefixCarriers

/-!
# Raw suspended targets at actual terminal-prefix returns

Status: UNCOMPILED CANDIDATE.
The actual prefix records every input occurrence before waiting-key deduplication.
Its union operations join the original raw targets to the returned winner.
An actual entry and its terminal partition identify the source bucket.
The full emitted-branch history and finite joint assignment remain open.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}
attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- Actual prefix success retains duplicate input occurrences and joins their raw targets. -/
theorem run_raw_target_incidence
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : EnumerationState.State Symbol EnumGuard)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (observed : ExceptT.run (run fuel first rest waiting before) =
      [.ok ((recorded, winner, moved), after)]) :
    recorded = (first :: rest).map (fun sc => roots sc.var) ∧
      after.values = before.values ∧
      ∀ sc ∈ first :: rest, UnionFind.SameClass after.representatives winner sc.var := by
  have success : Success (run fuel first rest waiting) before (recorded, winner, moved) after := by
    rw [Success, observed]
    exact List.mem_singleton_self _
  unfold run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel
    (first :: rest) before scanned actualRecorded ⟨rfl, paths⟩ scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  let selected : List Nat := rest.foldl
    (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united :=
    terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
      (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, _count, path⟩ := merging_representative before.values roots selected
    fuel first.var actualWinner united resolved joined resolution
  obtain ⟨resultSame, afterSame⟩ := (success_pure
    (actualRecorded, actualWinner, EnumerationCanonicalWaiting.moveMany actualWinner
      (EnumerationBuilderCaches.canonicalIds (actualRecorded.filter (fun key => key != actualWinner))) waiting)
    (recorded, winner, moved) resolved after).mp final
  have recordedEq : recorded = actualRecorded := congrArg Prod.fst resultSame
  have winnerEq : winner = actualWinner := congrArg
    (fun result : List Nat × Nat × EnumerationWaitingIndex.Waiting => result.2.1) resultSame
  subst recorded
  subst winner
  subst after
  refine ⟨recordedSame, resolvedValid.values, ?_⟩
  have selectedMember : ∀ sc ∈ first :: rest, roots sc.var ∈ selected := by
    intro sc member
    apply (resolve_members roots rest [roots first.var] (roots sc.var)).mpr
    rcases List.mem_cons.mp member with rfl | present
    · exact Or.inl (by simp)
    · exact Or.inr ⟨sc, present, rfl⟩
  intro sc present
  exact UnionFind.sameClass_trans
    (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
    ((resolvedValid.joined first.var sc.var).mpr
      (Or.inr ⟨selectedMember first (by simp), selectedMember sc present⟩))

end MicroCFTA.SourcePruningEnumerationTerminalPrefix

namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual entry's terminal obligations retain their raw targets at the actual joined endpoint. -/
theorem entered_terminal_prefix_raw_targets
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (entryFuel prefixFuel uv : Nat)
    (before entered joined : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : InternedConstructorTemplates.Value Symbol NativeGuard)
    (total : UnionFind.Total before.representatives)
    (entry : Success (enter heap entryFuel uv) before (target, handle, bucket, decoded) entered)
    (first : Suspended) (rest descendants : List Suspended)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants))
    (waiting : EnumerationWaitingIndex.Waiting) (recorded : List Nat) (winner : Nat)
    (moved : EnumerationWaitingIndex.Waiting) (roots : Nat → Nat)
    (paths : Roots entered.representatives roots)
    (processed : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      prefixFuel first rest waiting entered) = [.ok ((recorded, winner, moved), joined)]) :
    ∃ size, UnionFind.Reaches before.representatives uv target size ∧
      before.values[target]? = some (.unenumerated (some handle) bucket) ∧
      joined.values[target]? = some (.unenumerated (some handle) bucket) ∧
      recorded = (bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie)).map
        (fun sc => roots sc.var) ∧
      ∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
        UnionFind.SameClass joined.representatives winner sc.var := by
  obtain ⟨size, path, stored, values, _lookup, _histories, _expansion⟩ :=
    enter_recorded_bucket_origin heap entryFuel uv before entered target handle bucket decoded total entry
  obtain ⟨recordedSame, joinedValues, rawTargets⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_raw_target_incidence prefixFuel first rest waiting
      entered joined recorded winner moved roots paths processed
  have terminalMembers : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
    simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
  refine ⟨size, path, stored, ?_, ?_, ?_⟩
  · rw [joinedValues, values]
    exact stored
  · rw [terminalMembers]
    exact recordedSame
  · intro sc present atRoot
    apply rawTargets sc
    rw [← terminalMembers]
    apply List.mem_filter.mpr
    refine ⟨present, ?_⟩
    simp only [(EqualityTrie.nil_mem sc.trie).mp atRoot, EqualityTrie.isTerminal]

end MicroCFTA.SourcePruningEnumerationEntry
