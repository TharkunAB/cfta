import MicroCFTA.SourcePruningEnumerationChildCompletion
import MicroCFTA.SourcePruningEnumerationCachedTerminalLanguage
import MicroCFTA.SourcePruningEnumerationCachedPrepareLanguage
import MicroCFTA.SourcePruningEnumerationTerminalBucketLanguage

/-!
# Assignment language of actual stable child observations

Each branch compares its actual stable worker with one canonical receipt.
The terminal partition retains the full bucket. Ordinary fresh slots do too.
Other nonterminal slots omit the bucket, as in the actual shallow action.
No accepted raw row is replaced by a cache candidate on rejection.
-/
namespace MicroCFTA.SourcePruningEnumerationChildCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
variable {width : Nat}

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Each actual successful row has exactly its stored assignment restrictions. -/
theorem stable_semantics
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (ranges : Ranges checkEmpty bucket incoming beforeCaller before memos.query)
    {r n p h k : Nat} {raw : Raw} {afterCaller : Caller width} {after : Cached}
    {savedQueries : Queries} {outer : EnumerationState.State Symbol Constraint}
    {waiting : EnumerationWaitingIndex.Waiting}
    (observed : ∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
      SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
        P H (k + extraIndex) bucket incoming beforeCaller before memos.query =
        ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol)
      (fragment : Fragments.Fragment Symbol) (output : EnumerationState.State Symbol Constraint),
      Except.ok (fragment, output) ∈ raw →
        (Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output ↔
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient incoming (Fragments.fill assignment fragment) ∧
          ∀ sc ∈ (match incoming with
            | .node _ _ _ _ => bucket
            | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []),
            Suspended.Holds assignment (Fragments.fill assignment fragment) sc) := by
  by_cases empty : incoming = .empty
  · have actual := observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
    have projected := congrArg (fun result => result.1.1) actual
    have rawSame : [] = raw := by
      simpa only [SourcePruningEnumerationChildDispatch.run, ite_eq_left empty,
        Except.ok.injEq, Option.some.injEq] using projected
    intro _ambient _residualMeaning _assignment _fragment _output member
    rw [← rawSame] at member
    cases member
  · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
          have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
            simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
          exact List.any_eq_false.mpr (List.filter_eq_nil_iff.mp filtered)
        obtain ⟨action, indexFuel, rows, prepared, cachedRun, rawRun, shape, rowMeaning⟩ :=
          SourcePruningEnumerationCachedPrepare.complete_semantics beforeCaller.checked.native.machine.heap
            before incoming bucket roots initial.ready.semantic.ready.semantic.1.normal.facts.coherent
            available closed safe.1 realized paths counts flags bounded (fun _ => noTerminal)
        rcases shape with ⟨emptyValue, _emptyRows⟩ | ⟨next, _nonempty, rowsSame, _rest⟩
        · exact (empty emptyValue).elim
        · have cachedAt := cachedRun k
          rw [Nat.add_comm indexFuel k] at cachedAt
          have canonicalObserved :
              SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (k + indexFuel)
                bucket incoming beforeCaller before memos.query =
                ((.ok (some [.ok (.hole before.core.counter, next.core)]),
                  beforeCaller, memos.query, before.core, before.waiting), some next) := by
            simp only [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
              ite_eq_right empty, partitioned, prepared, cachedAt, rowsSame, rawRun,
              List.map_cons, List.map_nil]
          have actualObserved :
              SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (k + indexFuel)
                bucket incoming beforeCaller before memos.query =
                ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
            simpa only [Nat.add_zero] using
              observed 0 0 p h indexFuel (Nat.le_refl _) (Nat.le_refl _)
          have same : raw = [.ok (.hole before.core.counter, next.core)] ∧
              afterCaller = beforeCaller ∧ savedQueries = memos.query ∧
              outer = before.core ∧ waiting = before.waiting ∧ after = next := by
            simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
              actualObserved.symm.trans canonicalObserved
          obtain ⟨rawSame, callerSame, _queriesSame, _outerSame, _waitingSame, _cacheSame⟩ := same
          intro ambient residualMeaning assignment fragment output member
          have pairSame : (fragment, output) = (.hole before.core.counter, next.core) :=
            Except.ok.inj (List.mem_singleton.mp (by simpa only [rawSame] using member))
          have fragmentSame : fragment = .hole before.core.counter := congrArg Prod.fst pairSame
          have outputSame : output = next.core := congrArg Prod.snd pairSame
          have accepted :
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment next.core ↔
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                ambient incoming (assignment before.core.counter) ∧
              ∀ sc ∈ (match incoming with | .node _ _ _ _ => bucket | _ => []),
                Suspended.Holds assignment (assignment before.core.counter) sc := by
            have semantic := rowMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient residualMeaning assignment
            constructor
            · intro satisfied
              have restrictions := semantic.mp ⟨.hole before.core.counter, next,
                by simp only [rowsSame, List.mem_singleton], satisfied⟩
              cases incoming <;> exact restrictions
            · intro restrictions
              obtain ⟨otherFragment, row, rowMember, satisfied⟩ :=
                semantic.mpr (by cases incoming <;> exact restrictions)
              have rowSame : row = next :=
                congrArg Prod.snd (List.mem_singleton.mp (by simpa only [rowsSame] using rowMember))
              simpa only [rowSame] using satisfied
          have effectiveSame :
              (match incoming with
                | .node _ _ _ _ => bucket
                | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []) =
              (match incoming with | .node _ _ _ _ => bucket | _ => []) := by
            cases incoming <;> simp [noTerminal]
          simpa only [callerSame, fragmentSame, outputSame, Fragments.fill, effectiveSame] using accepted
      | cons first rest =>
        have terminal : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
          simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
        have below : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) = descendants := by
          simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
        have terminalSubset : first :: rest ⊆ bucket := by
          intro sc member
          rw [← terminal] at member
          exact (List.mem_filter.mp member).1
        have descendantsSubset : descendants ⊆ bucket := by
          intro sc member
          rw [← below] at member
          exact (List.mem_filter.mp member).1
        have terminalAny : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
          have firstMember : first ∈ bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) := by
            rw [terminal]
            exact List.mem_cons_self
          obtain ⟨member, isTerminal⟩ := List.mem_filter.mp firstMember
          exact List.any_eq_true.mpr ⟨first, member, isTerminal⟩
        have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
          fun sc member => bounded sc (terminalSubset member)
        have activePending : InputsPending before.core (first :: rest) := by
          intro held fragment stored sc member
          exact pending held fragment stored sc (terminalSubset member)
        obtain ⟨
          r0, n0, p0, h0, k0, recorded, winner, joined, foldRows, _foldCaller, _foldQueries, _foldFinal,
          _foldInventory, folded, canonicalRaw, reachedCaller, canonicalOuter, canonicalQueries, _final,
          _next, resultCache, _prefixRun, recordedSame, winnerMember, _movedSame, _joinedSame,
          _joinedFlagsSame, _prefixRoots, _prefixCounts, _joinedFlags, _cachedFoldRun, _foldRun, foldShape,
          _foldPost, _foldQuerySame, _foldCounter, _foldForest, _foldPaths, _foldStorage, _foldRealized,
          _foldedRoot, _foldPending, _foldCounts, _foldWaiting, _foldFlags, _foldEliminated,
          _foldCompleted, _foldedFrame, _foldedSafe, _foldedOrigin, _terminalRun, _post, _querySame,
          canonicalRun, _resultCounter, _resultPaths, _resultStorage, _resultRealized, _resultCounts,
          _resultFlags, _resultFrame, _resultSafe, _resultProtected, _resultOrigin, _resultAllowed,
          _rejectedCache, rejectedBranch, completedBranch, semantic⟩ :=
          SourcePruningEnumerationCachedTerminalAdapter.complete_semantics formulas solver inventory
            beforeCaller before checkEmpty first rest incoming descendants roots memos initial safe paths counts flags
            activeBounded activePending realized empty available closed
            (fun sc member => bounded sc (descendantsSubset member))
            (ranges empty first rest descendants partitioned)
        have canonicalObserved :
            SourcePruningEnumerationChildDispatch.run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0)
              (k + k0) bucket incoming beforeCaller before memos.query =
              ((.ok (some canonicalRaw), reachedCaller, canonicalQueries, canonicalOuter, joined.waiting),
                some resultCache) := by
          rw [SourcePruningEnumerationChildDispatch.terminal checkEmpty _ _ _ _ _ bucket incoming
            beforeCaller before memos.query first rest descendants partitioned]
          simpa only [Nat.add_comm] using canonicalRun r n (max p p0) (max h h0) k
            (Nat.le_max_right p p0) (Nat.le_max_right h h0)
        have actualObserved := observed r0 n0 (max p p0) (max h h0) k0
          (Nat.le_max_left p p0) (Nat.le_max_left h h0)
        have same : raw = canonicalRaw ∧ afterCaller = reachedCaller ∧
            savedQueries = canonicalQueries ∧ outer = canonicalOuter ∧
            waiting = joined.waiting ∧ after = resultCache := by
          simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
            actualObserved.symm.trans canonicalObserved
        obtain ⟨rawSame, callerSame, _queriesSame, _outerSame, _waitingSame, _cacheSame⟩ := same
        intro ambient residualMeaning assignment fragment output member
        rw [rawSame] at member
        have singleton : ∃ written, canonicalRaw = [.ok (.hole winner, written)] := by
          rcases foldShape with rejectedFold | completedFold
          · have nilRaw := (rejectedBranch rejectedFold).1
            rw [nilRaw] at member
            cases member
          · obtain ⟨_incomingK, _oldNode, _oldScs, _read, written, replacement, _handle,
              _cacheSame, _outerSame, _reading, _frame, _incomingRun, _writePrefix, _afterSame,
              _stored, _storage, _realized, _incomingPost, _unfolding, _cacheRun, _counter,
              _representatives, _paths, _counts, _waiting, _flags, _expandable, rawShape, _rest⟩ :=
                completedBranch completedFold
            by_cases replacementEmpty : replacement = .empty
            · rw [rawShape, ite_eq_left replacementEmpty] at member
              cases member
            · exact ⟨written.core, by simpa only [ite_eq_right replacementEmpty] using rawShape⟩
        obtain ⟨written, singletonRaw⟩ := singleton
        have pairSame : (fragment, output) = (.hole winner, written) :=
          Except.ok.inj (List.mem_singleton.mp (by simpa only [singletonRaw] using member))
        have fragmentSame : fragment = .hole winner := congrArg Prod.fst pairSame
        have accepted :
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient reachedCaller.checked.native.machine.heap) residualMeaning assignment output ↔
            (Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
              ∀ sc ∈ rest, assignment first.var = assignment sc.var) ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                ambient incoming (assignment winner) ∧
              ∀ sc ∈ descendants, Suspended.Holds assignment (assignment winner) sc := by
          have meaning := semantic ambient residualMeaning assignment
          constructor
          · intro satisfied
            exact meaning.mp ⟨fragment, output, member, satisfied⟩
          · intro restrictions
            obtain ⟨otherFragment, otherOutput, otherMember, satisfied⟩ := meaning.mpr restrictions
            have otherPair : (otherFragment, otherOutput) = (.hole winner, written) :=
              Except.ok.inj (List.mem_singleton.mp (by simpa only [singletonRaw] using otherMember))
            have outputSame : otherOutput = output :=
              (congrArg Prod.snd otherPair).trans (congrArg Prod.snd pairSame).symm
            simpa only [outputSame] using satisfied
        have bucketMeaning := SourcePruningEnumerationTerminalBucketLanguage.restrictions_iff
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core
          bucket first rest descendants roots recorded winner
          (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming)
          paths recordedSame winnerMember partitioned
        have effectiveSame :
            (match incoming with
              | .node _ _ _ _ => bucket
              | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []) = bucket := by
          cases incoming <;> simp [terminalAny]
        simpa only [callerSame, fragmentSame, Fragments.fill, effectiveSame] using accepted.trans bucketMeaning

end MicroCFTA.SourcePruningEnumerationChildCompletion
