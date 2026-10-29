import MicroCFTA.SourcePruningEnumerationFoldStorageProgress
import MicroCFTA.SourcePruningEnumerationTerminalLanguage
import MicroCFTA.EnumerationCompressionFrame

namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompleteness EnumerationDependencies
open EnumerationStorageProgress SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- Original terminal obligations derive the winner's chosen term and retain the original assignment. -/
theorem observed_chosen_pendingSize
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (roots : Nat → Nat)
    (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (safe : Safe before) (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest)) (realized : PendingRealized heap before)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (chosen : Term Symbol)
    (satisfied : Satisfies language meaning assignment before)
    (terminal : ∀ sc ∈ first :: rest, EqualityTrie.isTerminal sc.trie = true)
    (held : ∀ sc ∈ first :: rest, Suspended.Holds assignment chosen sc)
    {fuel : Nat} {recorded : List Nat} {winner : Nat} {moved : EnumerationWaitingIndex.Waiting}
    {joined : EnumerationState.State Symbol EnumGuard}
    (observed : ExceptT.run (run fuel first rest waiting before) =
      [.ok ((recorded, winner, moved), joined)]) :
    StorageValid joined ∧ PendingAt joined winner ∧ IsRoot joined.representatives winner ∧
      pendingSize joined assignment = pendingSize before assignment ∧
      assignment winner = chosen ∧
      (∀ source ∈ recorded, assignment source = chosen) ∧ Satisfies language meaning assignment joined := by
  obtain ⟨bound, canonicalRecorded, canonicalWinner, canonicalMoved, _scanned, _united,
    canonicalJoined, running, _scanning, _unions, _resolution, recordedSame, _movedSame,
    winnerMember, winnerFixed, joinedPaths, _joinedCounts, joinedSame, joinedStorage,
    _joinedRealized, winnerPending, _sourcesPending, _distinct, _ordered, _keys, _classes, models⟩ :=
    run_complete_semantics heap before first rest waiting roots paths counts safe bounded pending realized
  have canonicalObserved : ExceptT.run (run bound first rest waiting before) =
      [.ok ((canonicalRecorded, canonicalWinner, canonicalMoved), canonicalJoined)] := by
    simpa only [Nat.add_zero] using running 0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := run_unique first rest waiting before observed canonicalObserved
  have rootAssignment (uv : Nat) : assignment (roots uv) = assignment uv := by
    obtain ⟨size, path⟩ := paths uv
    exact (satisfied.1.1 uv (roots uv)
      ⟨roots uv, size, path, .root (UnionFind.reaches_terminal path)⟩).symm
  have equalHere : ∀ sc ∈ first :: rest, assignment sc.var = chosen := by
    intro sc member
    exact ((EnumerationSemantics.terminal_holds assignment chosen sc (terminal sc member)).mp
      (held sc member)).symm
  have winnerChosen : assignment winner = chosen := by
    rw [recordedSame] at winnerMember
    obtain ⟨sc, member, selected⟩ := List.mem_map.mp winnerMember
    rw [← selected, rootAssignment sc.var]
    exact equalHere sc member
  have sourcesChosen : ∀ source ∈ recorded, assignment source = chosen := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, selected⟩ := List.mem_map.mp member
    rw [← selected, rootAssignment sc.var]
    exact equalHere sc present
  have winnerSelected : roots winner ∈ recorded := by simpa only [winnerFixed] using winnerMember
  have winnerRoot : IsRoot joined.representatives winner := by
    apply (root_iff joined.representatives
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) joinedPaths winner).mpr
    simp only [EnumerationCanonicalUnion.mergedRoots, ite_eq_left winnerSelected]
  have sameCost : pendingSize joined assignment = pendingSize before assignment := by
    rw [joinedSame]
    rfl
  have joinedModel : Satisfies language meaning assignment joined :=
    (models language meaning assignment).mpr ⟨satisfied, fun sc member =>
      (equalHere first List.mem_cons_self).trans (equalHere sc (List.mem_cons_of_mem first member)).symm⟩
  exact ⟨joinedStorage, winnerPending, winnerRoot, sameCost, winnerChosen, sourcesChosen, joinedModel⟩

end MicroCFTA.SourcePruningEnumerationTerminalPrefix

namespace MicroCFTA.SourcePruningEnumerationTerminal
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompleteness EnumerationDependencies
open EnumerationStorageProgress InternedConstructorTemplates SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] terminalMonadList

/-- Actual terminal stages charge at most one chosen child and return its same assigned hole. -/
theorem observed_stages_chosen_pendingSize
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (beforeCaller : Caller width) (before : Core EnumGuard)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (safe : Safe before) (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (chosen : Term Symbol)
    (satisfied : Satisfies language meaning assignment before)
    (terminal : ∀ sc ∈ first :: rest, EqualityTrie.isTerminal sc.trie = true)
    (held : ∀ sc ∈ first :: rest, Suspended.Holds assignment chosen sc)
    (nonempty : incoming ≠ .empty)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (joined : Core EnumGuard) (foldCaller : Caller width) (foldQueries : Queries) (folded : Core EnumGuard)
    (oldNode : Option Nat) (oldScs : List Suspended) (read after : Core EnumGuard)
    (afterCaller : Caller width) (savedQueries : Queries) (handle : Nat)
    (prefixActual : ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)])
    (foldActual : SourcePruningEnumerationFold.run checkEmpty n p h recorded beforeCaller joined winner queries =
      (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, folded))
    (incomingActual : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h foldCaller folded
      winner incoming incomingScs foldQueries =
        (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read))
    (reading : ExceptT.run (getValue r winner folded) = [.ok (.unenumerated oldNode oldScs, read)])
    (writing : ExceptT.run ((do
      setValue winner (.unenumerated (some handle) (incomingScs ++ oldScs))
      inheritAncestry winner) read) = [.ok ((), after)]) :
    run checkEmpty r n p h first rest waiting beforeCaller before incoming incomingScs queries =
        (.ok (some [.ok (.hole winner, after)]), afterCaller, savedQueries, read, moved) ∧
      pendingSize after assignment ≤ pendingSize before assignment + NumberedTerms.size chosen ∧
      Fragments.fill assignment (.hole winner : Fragments.Fragment Symbol) = chosen := by
  obtain ⟨joinedStorage, winnerPending, winnerRoot, prefixCost, winnerChosen, sourceChosen, _joinedModel⟩ :=
    SourcePruningEnumerationTerminalPrefix.observed_chosen_pendingSize
      beforeCaller.checked.native.machine.heap before first rest waiting roots paths counts safe bounded pending
      realized language meaning assignment chosen satisfied terminal held prefixActual
  have sourceEqual : ∀ source ∈ recorded, assignment source = assignment winner := by
    intro source member
    exact (sourceChosen source member).trans winnerChosen.symm
  obtain ⟨_foldedPending, foldedRepresentatives, foldCost⟩ :=
    SourcePruningEnumerationFold.singleton_pendingSize_le checkEmpty n p h recorded beforeCaller joined winner
      queries foldCaller foldQueries folded assignment winnerPending sourceEqual foldActual
  have foldedTotal : UnionFind.Total folded.representatives := by
    rw [foldedRepresentatives]
    exact joinedStorage.total
  have foldedRoot : IsRoot folded.representatives winner := by
    rw [foldedRepresentatives]
    exact winnerRoot
  have readingSuccess : EnumerationCorrectness.Success
      (getValue r winner) folded (.unenumerated oldNode oldScs) read := by
    rw [EnumerationCorrectness.Success, reading]
    exact List.mem_singleton_self _
  obtain ⟨compression, resolved, size, beforePath, _afterPath, stored⟩ :=
    EnumerationCompressionFrame.getValue_frame r winner folded read (.unenumerated oldNode oldScs)
      foldedTotal readingSuccess
  obtain ⟨_winnerSize, winnerPath⟩ := foldedRoot
  have sameRoot : resolved = winner := (UnionFind.reaches_unique beforePath winnerPath).1
  subst resolved
  have readStored : read.values[winner]? = some (.unenumerated oldNode oldScs) := by
    rw [compression.values]
    exact stored
  have writtenValues : after.values = read.values.set winner
      (.unenumerated (some handle) (incomingScs ++ oldScs)) := by
    change [Except.ok ((), {read with
      values := read.values.set winner (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = winner then
        (read.expansionAncestry ++ read.recursionAncestry winner).eraseDups
        else read.recursionAncestry other})] = [Except.ok ((), after)] at writing
    have same : {read with
        values := read.values.set winner (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = winner then
          (read.expansionAncestry ++ read.recursionAncestry winner).eraseDups
          else read.recursionAncestry other} = after := by
      simpa only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] using writing
    exact (congrArg EnumerationState.State.values same).symm
  have writeCost := incoming_values_pendingSize read after winner handle oldNode oldScs
    (incomingScs ++ oldScs) assignment readStored writtenValues
  have readCost : pendingSize read assignment = pendingSize folded assignment := by
    unfold pendingSize
    rw [compression.values]
  have extraBound : (if oldNode.isSome then 0 else NumberedTerms.size (assignment winner)) ≤
      NumberedTerms.size (assignment winner) := by split <;> omega
  have cost : pendingSize after assignment ≤ pendingSize before assignment + NumberedTerms.size chosen := by
    calc
      pendingSize after assignment = pendingSize read assignment +
          (if oldNode.isSome then 0 else NumberedTerms.size (assignment winner)) := writeCost
      _ ≤ pendingSize read assignment + NumberedTerms.size (assignment winner) := Nat.add_le_add_left extraBound _
      _ = pendingSize folded assignment + NumberedTerms.size chosen := by rw [readCost, winnerChosen]
      _ ≤ pendingSize joined assignment + NumberedTerms.size chosen := Nat.add_le_add_right foldCost _
      _ = pendingSize before assignment + NumberedTerms.size chosen := by rw [prefixCost]
  have terminalActual : run checkEmpty r n p h first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some [.ok (.hole winner, after)]), afterCaller, savedQueries, read, moved) := by
    simp only [run, ite_eq_right nonempty, prefixActual, foldActual, incomingActual, List.map_cons, List.map_nil]
  refine ⟨terminalActual, cost, ?_⟩
  simpa only [Fragments.fill] using winnerChosen

end MicroCFTA.SourcePruningEnumerationTerminal
