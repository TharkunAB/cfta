import MicroCFTA.SourcePruningEnumerationCachedFoldCompletion
import MicroCFTA.SourcePruningEnumerationCachedIncoming

namespace MicroCFTA.SourcePruningEnumerationCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- Derive the admitted nonempty terminal run and its logical native caches. -/
theorem complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checkEmpty : Bool) (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (nonempty : incoming ≠ .empty)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingBounded : ∀ sc ∈ incomingScs, sc.var < before.core.counter)
    (ranges : ∀ (prefixFuel : Nat) (recorded : List Nat) (winner : Nat)
      (moved : EnumerationWaitingIndex.Waiting) (joined : EnumerationState.State Symbol Constraint),
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run prefixFuel first rest before.waiting before.core) =
        [.ok ((recorded, winner, moved), joined)] →
      SourcePruningEnumerationFold.Ranges checkEmpty recorded beforeCaller joined winner memos.query ∧
      ∀ (foldFuel P H : Nat) (foldCaller : Caller width)
        (folded : EnumerationState.State Symbol Constraint) (foldQueries : Queries),
        SourcePruningEnumerationFold.run checkEmpty foldFuel P H recorded beforeCaller joined winner memos.query =
          (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, folded) →
        match folded.values[winner]? with
        | some (.unenumerated (some oldHandle) _) =>
            match lookupNode foldCaller.checked.native.machine.heap oldHandle with
            | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                foldCaller.checked
            | none => True
        | _ => True) :
    ∃ (r n p h : Nat) (recorded : List Nat) (winner : Nat)
      (joined : EnumerationExpandableIndex.Cached Symbol Constraint)
      (foldRows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (foldCaller : Caller width) (foldQueries : Queries) (foldFinal : Memos) (foldInventory : Inventory)
      (folded : EnumerationExpandableIndex.Cached Symbol Constraint)
      (raw : TerminalRaw) (afterCaller : Caller width) (outer : EnumerationState.State Symbol Constraint)
      (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        (r + extra) first rest before.waiting before.core) =
        [.ok ((recorded, winner, joined.waiting), joined.core)]) ∧
      recorded = (first :: rest).map (fun sc => roots sc.var) ∧ winner ∈ recorded ∧
      joined.waiting = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))) before.waiting ∧
      joined.core = {before.core with representatives := joined.core.representatives} ∧
      joined.expandable = before.expandable ∧
      Roots joined.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        joined.core.values joined.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        beforeCaller.checked.native.machine.heap
        ((joined.core.values[slot]?).getD .eliminated) = some (joined.expandable slot)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationCachedFold.run checkEmpty (n + extra) P H recorded
          beforeCaller joined winner memos.query =
          ((.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
            foldCaller, foldQueries, folded.core), some folded)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationFold.run checkEmpty (n + extra) P H recorded
          beforeCaller joined.core winner memos.query =
          (.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
            foldCaller, foldQueries, folded.core)) ∧
      (foldRows = [] ∨ foldRows = [((), folded)]) ∧
      Post formulas solver foldInventory beforeCaller foldCaller foldFinal ∧ foldFinal.query = foldQueries ∧
      folded.core.counter = joined.core.counter ∧ folded.core.representatives = joined.core.representatives ∧
      Roots folded.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      StorageValid folded.core ∧ PendingRealized foldCaller.checked.native.machine.heap folded.core ∧
      IsRoot folded.core.representatives winner ∧ PendingAt folded.core winner ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        folded.core.values folded.waiting ∧ folded.waiting = joined.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        foldCaller.checked.native.machine.heap
        ((folded.core.values[slot]?).getD .eliminated) = some (folded.expandable slot)) ∧
      (∀ (slot : Nat), joined.core.values[slot]? = some .eliminated →
        folded.core.values[slot]? = some .eliminated) ∧
      (foldRows = [((), folded)] → ∀ source ∈ recorded, source ≠ winner →
        folded.core.values[source]? = some .eliminated) ∧
      (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationTerminal.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
          first rest before.waiting beforeCaller before.core incoming incomingScs memos.query =
          (.ok (some raw), afterCaller, savedQueries, outer, joined.waiting)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      (foldRows = [] → raw = [] ∧ afterCaller = foldCaller ∧ savedQueries = foldQueries ∧
        outer = folded.core ∧ final = foldFinal ∧ next = foldInventory) ∧
      (foldRows = [((), folded)] →
        ∃ (k : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
          (read : EnumerationState.State Symbol Constraint)
          (after : EnumerationExpandableIndex.Cached Symbol Constraint) (replacement : Node) (handle : Nat),
          outer = read ∧
          (∀ extra, ExceptT.run (getValue (r + extra) winner folded.core) =
            [.ok (.unenumerated oldNode oldScs, read)]) ∧
          EnumerationCompressionFrame.Frame folded.core read ∧
          (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationIncomingNode.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
              foldCaller folded.core winner incoming incomingScs foldQueries =
              (.ok (some (if replacement = .empty then [] else [.ok ((), after.core)])),
                afterCaller, savedQueries, read)) ∧
          ExceptT.run ((do
            setValue winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            inheritAncestry winner) read) = [.ok ((), after.core)] ∧
          after.core = {read with
            values := read.values.set winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            recursionAncestry := fun other => if other = winner then
              (read.expansionAncestry ++ read.recursionAncestry winner).eraseDups else read.recursionAncestry other} ∧
          after.core.values[winner]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
          StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
          Post formulas solver next foldCaller afterCaller final ∧
          Cache.Extends foldFinal.unfolding final.unfolding ∧
          (∀ extra, (SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
            (k + extra) winner (.unenumerated (some handle) (incomingScs ++ oldScs)) incomingScs []
            (EnumerationExpandableIndex.frame read folded)).map (EnumerationExpandableIndex.frame after.core) = some after) ∧
          after.core.counter = folded.core.counter ∧ after.core.representatives = read.representatives ∧
          Roots after.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
          EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
            after.core.values after.waiting ∧
          after.waiting = EnumerationCanonicalWaiting.count
            (EnumerationCanonicalUnion.mergedRoots roots recorded winner) 1 incomingScs joined.waiting ∧
          (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
            afterCaller.checked.native.machine.heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          after.expandable = (fun slot => if slot = winner then
            !(MergedOrdinaryHeight.recursiveBoundary replacement && (incomingScs ++ oldScs).isEmpty)
            else folded.expandable slot) ∧
          raw = (if replacement = .empty then [] else [.ok (.hole winner, after.core)]) ∧
          FragmentBound after.core.counter (.hole winner : Fragments.Fragment Symbol) ∧
          Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
          encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
          (oldNode = none → replacement = incoming ∧ afterCaller = foldCaller ∧
            savedQueries = foldQueries ∧ final = foldFinal ∧ next = foldInventory) ∧
          (∀ oldHandle, oldNode = some oldHandle →
            ∃ (old query : Node) (queried : Checked width),
              lookupNode foldCaller.checked.native.machine.heap oldHandle = some old ∧
              next.source = foldCaller.checked.native.machine.heap ∧ next.roots = foldInventory.roots ++ [incoming, old] ∧
              SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old foldCaller.checked query queried foldFinal ∧
              (∀ ambient term,
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
              (checkEmpty = false → replacement = query ∧
                afterCaller = SourceCurrentAllocatedPartialState.advance foldCaller queried foldCaller.fourth foldCaller.merge ∧
                final = foldFinal))) := by
  obtain ⟨prefixFuel, recorded, winner, moved, _scanned, _united, joined, prefixRun,
    _scanRun, _unionRun, _winnerRun, recordedSame, movedSame, winnerMember, rootWinner,
    prefixRoots, prefixCounts, joinedSame, joinedStorage, joinedRealized, winnerPending,
    recordedPending, _keysNodup, _keysSorted, _keysMember⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_complete beforeCaller.checked.native.machine.heap
      before.core first rest before.waiting roots paths counts safe bounded pending realized
  have joinedRoot : IsRoot joined.representatives winner := by
    apply (root_iff joined.representatives _ prefixRoots winner).mpr
    simp only [EnumerationCanonicalUnion.mergedRoots, rootWinner, ite_self]
  have joinedFlags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((joined.values[slot]?).getD .eliminated) = some (before.expandable slot) := by
    simpa only [congrArg EnumerationState.State.values joinedSame] using flags
  let joinedCache : EnumerationExpandableIndex.Cached Symbol Constraint :=
    ⟨joined, before.expandable, moved⟩
  obtain ⟨foldFuel, foldP, foldH, foldRows, foldCaller, foldQueries, foldFinal, foldInventory,
    folded, cachedFoldRun, foldPost, foldQuerySame, foldCounter, foldForest, foldPaths,
    foldStorage, foldRealized, foldCounts, foldWaiting, foldFlags, foldShape, foldPending,
    foldEliminated, foldCompleted⟩ :=
    SourcePruningEnumerationCachedFoldCompletion.complete formulas solver inventory beforeCaller
      joinedCache recorded checkEmpty winner memos
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) initial joinedStorage
      joinedRealized prefixRoots prefixCounts joinedFlags winnerPending
      (fun source member => .inl (recordedPending source member))
      (ranges prefixFuel recorded winner moved joined (by simpa only [Nat.add_zero] using prefixRun 0)).1
  have foldRun : ∀ extra P H, foldP ≤ P → foldH ≤ H →
      SourcePruningEnumerationFold.run checkEmpty (foldFuel + extra) P H recorded
        beforeCaller joined winner memos.query =
        (.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
          foldCaller, foldQueries, folded.core) := by
    intro extra P H enoughP enoughH
    rw [← SourcePruningEnumerationCachedFold.erase checkEmpty (foldFuel + extra) P H
      recorded beforeCaller joinedCache winner memos.query]
    exact congrArg Prod.fst (cachedFoldRun extra P H enoughP enoughH)
  have foldedRoot : IsRoot folded.core.representatives winner := by
    simpa only [foldForest] using joinedRoot
  rcases foldShape with rejected | completed
  · subst foldRows
    refine ⟨prefixFuel, foldFuel, foldP, foldH, recorded, winner, joinedCache, [],
      foldCaller, foldQueries, foldFinal, foldInventory, folded, [], foldCaller, folded.core,
      foldQueries, foldFinal, foldInventory, prefixRun, recordedSame, winnerMember, movedSame,
      joinedSame, rfl, prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, .inl rfl,
      foldPost, foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized,
      foldedRoot, foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
      ?_, foldPost, foldQuerySame, ?_, ?_⟩
    · intro extraRepresentative extraNative P H enoughP enoughH
      simp only [SourcePruningEnumerationTerminal.run, ite_eq_right nonempty,
        prefixRun extraRepresentative, foldRun extraNative P H enoughP enoughH, List.map_nil, joinedCache]
    · intro isRejected
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro isCompleted
      cases isCompleted
  · subst foldRows
    have foldedAvailable : Available foldCaller.checked.native.machine.heap incoming := by
      exact foldPost.effects.keeps.available incoming available
    have foldedBounded : ∀ sc ∈ incomingScs, sc.var < folded.core.counter := by
      intro sc member
      rw [foldCounter]
      change sc.var < joined.counter
      simpa only [congrArg EnumerationState.State.counter joinedSame] using incomingBounded sc member
    obtain ⟨incomingR, incomingN, incomingP, incomingH, k, oldNode, oldScs, read, afterCaller,
      savedQueries, final, next, replacement, handle, after, reading, frame, incomingRun,
      writePrefix, afterSame, afterStored, afterStorage, afterRealized, incomingPost,
      incomingQuerySame, unfolding, replacementAvailable, replacementClosed, encoded, decoded,
      cacheRun, afterCounter, afterRepresentatives, afterPaths, afterCounts, incomingWaiting,
      afterFlags, afterExpandable, optional, present⟩ :=
      SourcePruningEnumerationCachedIncoming.complete formulas solver foldInventory foldCaller
        folded checkEmpty winner incoming incomingScs foldFinal
        (EnumerationCanonicalUnion.mergedRoots roots recorded winner) foldPost.context foldStorage
        foldRealized foldPaths foldCounts foldFlags foldedRoot foldPending foldedAvailable closed
        foldedBounded ((ranges prefixFuel recorded winner moved joined
          (by simpa only [Nat.add_zero] using prefixRun 0)).2 foldFuel foldP foldH foldCaller
            folded.core foldQueries (by
              simpa only [Nat.add_zero, List.map_cons, List.map_nil] using
                foldRun 0 foldP foldH (by omega) (by omega)))
    have writeWaiting : after.waiting = EnumerationCanonicalWaiting.count
        (EnumerationCanonicalUnion.mergedRoots roots recorded winner) 1 incomingScs moved := by
      simpa only [foldWaiting] using incomingWaiting
    have winnerBound : winner < after.core.counter := by
      rw [afterStorage.aligned]
      exact (List.getElem?_eq_some_iff.mp afterStored).elim (fun inside _elementEquality => inside)
    simp only [foldQuerySame] at incomingRun optional
    refine ⟨prefixFuel + incomingR, foldFuel + incomingN, foldP + incomingP, foldH + incomingH,
      recorded, winner, joinedCache, [((), folded)], foldCaller, foldQueries, foldFinal,
      foldInventory, folded, (if replacement = .empty then [] else [.ok (.hole winner, after.core)]),
      afterCaller, read, savedQueries, final, next, ?_, recordedSame, winnerMember, movedSame,
      joinedSame, rfl, prefixRoots, prefixCounts, joinedFlags, ?_, ?_, .inr rfl, foldPost,
      foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
      foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted, ?_,
      foldPost.trans incomingPost, incomingQuerySame, ?_, ?_⟩
    · intro extra
      simpa only [Nat.add_assoc] using prefixRun (incomingR + extra)
    · intro extra P H enoughP enoughH
      simpa only [Nat.add_assoc] using
        cachedFoldRun (incomingN + extra) P H (by omega) (by omega)
    · intro extra P H enoughP enoughH
      simpa only [Nat.add_assoc] using foldRun (incomingN + extra) P H (by omega) (by omega)
    · intro extraRepresentative extraNative P H enoughP enoughH
      simp only [SourcePruningEnumerationTerminal.run, ite_eq_right nonempty, Nat.add_assoc,
        prefixRun (incomingR + extraRepresentative),
        foldRun (incomingN + extraNative) P H (by omega) (by omega), List.map_cons, List.map_nil, joinedCache]
      rw [Nat.add_left_comm prefixFuel incomingR extraRepresentative,
        Nat.add_left_comm foldFuel incomingN extraNative,
        incomingRun (prefixFuel + extraRepresentative) (foldFuel + extraNative) P H (by omega) (by omega)]
      by_cases empty : replacement = .empty <;> simp [empty]
    · intro isRejected
      cases isRejected
    · intro isCompleted
      refine ⟨k, oldNode, oldScs, read, after, replacement, handle, rfl, ?_, frame, ?_,
        writePrefix, afterSame, afterStored, afterStorage, afterRealized, incomingPost,
        unfolding, cacheRun, afterCounter, afterRepresentatives, afterPaths, afterCounts,
        writeWaiting, afterFlags, afterExpandable, rfl, winnerBound, replacementAvailable,
        replacementClosed, encoded, decoded, optional, present⟩
      · intro extra
        simpa only [Nat.add_assoc, Nat.add_left_comm prefixFuel incomingR extra] using
          reading (prefixFuel + extra)
      · intro extraRepresentative extraNative P H enoughP enoughH
        simpa only [Nat.add_assoc, Nat.add_left_comm prefixFuel incomingR extraRepresentative,
          Nat.add_left_comm foldFuel incomingN extraNative] using
          incomingRun (prefixFuel + extraRepresentative) (foldFuel + extraNative) P H (by omega) (by omega)

end MicroCFTA.SourcePruningEnumerationCachedTerminal
