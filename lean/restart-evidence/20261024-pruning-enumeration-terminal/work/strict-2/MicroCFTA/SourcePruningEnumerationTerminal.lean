import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.SourcePruningEnumerationFoldInvariants
import MicroCFTA.SourcePruningEnumerationIncomingNode

namespace MicroCFTA.SourcePruningEnumerationTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
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
variable {EnumGuard : Type} {width : Nat}
local notation "PrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationState.State Symbol EnumGuard))
local notation "FoldRaw" => List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol EnumGuard))
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome («Symbol» := Symbol) («Guard» := Constraint) width Node
local notation "WorkerOutcome" => SourceCurrentAllocatedConjunctionWorker.Outcome width

local instance terminalMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Run the terminal prefix, ordered fold and actual incoming merge. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationState.State Symbol EnumGuard × EnumerationWaitingIndex.Waiting :=
  if incoming = .empty then (.ok (some []), beforeCaller, queries, before, waiting)
  else
    match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest waiting before) with
    | [.ok ((recorded, winner, moved), joined)] =>
      match SourcePruningEnumerationFold.run checkEmpty nativeFuel p h recorded beforeCaller joined winner queries with
      | (foldResult, foldCaller, foldQueries, foldOuter) =>
        match foldResult with
        | .error foldFault => (.error (.inr (.inl foldFault)), foldCaller, foldQueries, foldOuter, moved)
        | .ok none => (.ok none, foldCaller, foldQueries, foldOuter, moved)
        | .ok (some foldRaw) =>
          match foldRaw with
          | [] => (.ok (some []), foldCaller, foldQueries, foldOuter, moved)
          | [.ok ((), folded)] =>
            match SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
                foldCaller folded winner incoming incomingScs foldQueries with
            | (incomingResult, afterCaller, savedQueries, read) =>
              match incomingResult with
              | .error incomingFault => (.error (.inr (.inl incomingFault)), afterCaller, savedQueries, read, moved)
              | .ok none => (.ok none, afterCaller, savedQueries, read, moved)
              | .ok (some incomingRaw) =>
                (.ok (some (incomingRaw.map fun row => match row with
                  | .error error => .error error
                  | .ok result => .ok (.hole winner, result.2))), afterCaller, savedQueries, read, moved)
          | stoppedRaw => (.error (.inr (.inr stoppedRaw)), foldCaller, foldQueries, foldOuter, moved)
    | prefixRaw => (.error (.inl prefixRaw), beforeCaller, queries, before, waiting)

/-- Adding incoming references gives the exact logical gained-only table. -/
theorem gained_correct
    (values : List (EnumerationState.UVarValue Symbol)) (target : Nat)
    (oldNode newNode : Option Nat) (incomingScs oldScs : List EnumerationState.Suspended)
    (roots : Nat → Nat) (waiting : EnumerationWaitingIndex.Waiting)
    (stored : values[target]? = some (.unenumerated oldNode oldScs))
    (counts : EnumerationCanonicalWaiting.Correct roots values waiting) :
    EnumerationCanonicalWaiting.Correct roots
      (values.set target (.unenumerated newNode (incomingScs ++ oldScs)))
      (EnumerationCanonicalWaiting.count roots 1 incomingScs waiting) := by
  have same : EnumerationCanonicalWaiting.replace («Symbol» := Symbol) roots
      (.unenumerated oldNode oldScs) (.unenumerated newNode (incomingScs ++ oldScs)) waiting =
      EnumerationCanonicalWaiting.count roots 1 incomingScs waiting := by
    funext key
    change EnumerationWaitingIndex.count 1
        ((incomingScs ++ oldScs).map fun sc => {sc with var := roots sc.var})
        (EnumerationWaitingIndex.count (-1) (oldScs.map fun sc => {sc with var := roots sc.var}) waiting) key =
      EnumerationWaitingIndex.count 1 (incomingScs.map fun sc => {sc with var := roots sc.var}) waiting key
    rw [EnumerationWaitingIndex.count_canonical 1 _ _
        (EnumerationWaitingIndex.count_canonical (-1) _ _ (EnumerationWaitingIndex.Correct.facts counts).1) key,
      EnumerationWaitingIndex.count_canonical 1 _ _ (EnumerationWaitingIndex.Correct.facts counts).1 key]
    congr 1
    simp only [EnumerationWaitingIndex.count_read, List.map_append,
      EnumerationWaitingIndex.occurrences_append, Int.one_mul, Int.neg_one_mul]
    omega
  simpa only [same] using EnumerationCanonicalWaiting.replace_correct roots values target
    (.unenumerated oldNode oldScs) (.unenumerated newNode (incomingScs ++ oldScs)) stored waiting counts

/-- Initial pending inputs and current bounds derive the complete terminal arm. -/
theorem run_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before) (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (nonempty : incoming ≠ .empty)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingBounded : ∀ sc ∈ incomingScs, sc.var < before.counter)
    (ranges : ∀ (prefixFuel : Nat) (recorded : List Nat) (winner : Nat)
      (moved : EnumerationWaitingIndex.Waiting) (joined : EnumerationState.State Symbol EnumGuard),
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run prefixFuel first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)] →
      SourcePruningEnumerationFold.Ranges checkEmpty recorded beforeCaller joined winner memos.query ∧
      ∀ (foldFuel P H : Nat) (foldCaller : Caller width)
        (folded : EnumerationState.State Symbol EnumGuard) (foldQueries : Queries),
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
      (moved : EnumerationWaitingIndex.Waiting) (joined : EnumerationState.State Symbol EnumGuard)
      (foldRaw : FoldRaw) (foldCaller : Caller width) (folded : EnumerationState.State Symbol EnumGuard)
      (foldQueries : Queries) (foldFinal : Memos) (foldInventory : Inventory)
      (raw : TerminalRaw) (afterCaller : Caller width) (outer : EnumerationState.State Symbol EnumGuard)
      (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run (r + extra) first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)]) ∧
      recorded = (first :: rest).map (fun sc => roots sc.var) ∧ winner ∈ recorded ∧
      moved = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))) waiting ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationFold.run checkEmpty (n + extra) P H recorded beforeCaller joined winner memos.query =
          (.ok (some foldRaw), foldCaller, foldQueries, folded)) ∧
      (foldRaw = [] ∨ foldRaw = [.ok ((), folded)]) ∧
      Post formulas solver foldInventory beforeCaller foldCaller foldFinal ∧ foldFinal.query = foldQueries ∧
      StorageValid folded ∧ PendingRealized foldCaller.checked.native.machine.heap folded ∧
      IsRoot folded.representatives winner ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        folded.values moved ∧
      (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
        run checkEmpty (r + extraRepresentative) (n + extraNative) P H first rest waiting
          beforeCaller before incoming incomingScs memos.query =
          (.ok (some raw), afterCaller, savedQueries, outer, moved)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      (foldRaw = [] → raw = [] ∧ afterCaller = foldCaller ∧ savedQueries = foldQueries ∧
        outer = folded ∧ final = foldFinal ∧ next = foldInventory) ∧
      (foldRaw = [.ok ((), folded)] →
        ∃ (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
          (read afterWrite : EnumerationState.State Symbol EnumGuard) (replacement : Node) (handle : Nat),
          outer = read ∧
          (∀ extra, ExceptT.run (getValue (r + extra) winner folded) =
            [.ok (.unenumerated oldNode oldScs, read)]) ∧
          EnumerationCompressionFrame.Frame folded read ∧
          (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationIncomingNode.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
              foldCaller folded winner incoming incomingScs foldQueries =
              (.ok (some (if replacement = .empty then [] else [.ok ((), afterWrite)])),
                afterCaller, savedQueries, read)) ∧
          ExceptT.run ((do
            setValue winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            inheritAncestry winner) read) = [.ok ((), afterWrite)] ∧
          afterWrite.values[winner]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
          StorageValid afterWrite ∧ PendingRealized afterCaller.checked.native.machine.heap afterWrite ∧
          EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
            afterWrite.values
            (EnumerationCanonicalWaiting.count (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
              1 incomingScs moved) ∧
          raw = (if replacement = .empty then [] else [.ok (.hole winner, afterWrite)]) ∧
          FragmentBound afterWrite.counter (.hole winner : Fragments.Fragment Symbol) ∧
          Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
          encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
          (oldNode = none → replacement = incoming ∧ afterCaller = foldCaller ∧
            savedQueries = foldQueries ∧ final = foldFinal ∧ next = foldInventory) ∧
          (∀ oldHandle, oldNode = some oldHandle →
            ∃ (old query : Node) (queried : SourceEqualityNativeDemand.State width),
              lookupNode foldCaller.checked.native.machine.heap oldHandle = some old ∧
              next.source = foldCaller.checked.native.machine.heap ∧
              next.roots = foldInventory.roots ++ [incoming, old] ∧
              SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old
                foldCaller.checked query queried foldFinal ∧
              (∀ ambient term,
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term))) := by
  obtain ⟨prefixFuel, recorded, winner, moved, _, _, joined, prefixRun, _, _, _, recordedSame,
    movedSame, winnerMember, rootWinner, prefixRoots, prefixCounts, joinedSame, joinedStorage,
    joinedRealized, winnerPending, recordedPending, _, _, _⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_complete beforeCaller.checked.native.machine.heap before
      first rest waiting roots paths counts safe bounded pending realized
  have joinedRoot : IsRoot joined.representatives winner := by
    apply (root_iff joined.representatives _ prefixRoots winner).mpr
    simp only [EnumerationCanonicalUnion.mergedRoots, rootWinner, ite_self]
  obtain ⟨foldFuel, foldP, foldH, foldRaw, foldCaller, folded, foldQueries, foldFinal, foldInventory,
    foldRun, foldPost, foldQuerySame, foldRealized, foldShape, foldCompleted, _, _, foldForest,
    foldCounter, _, _, _, _⟩ :=
    SourcePruningEnumerationFold.run_complete formulas solver inventory beforeCaller joined recorded
      checkEmpty winner memos initial joinedRealized winnerPending
      (fun source member => .inr (recordedPending source member))
      (ranges prefixFuel recorded winner moved joined (by simpa only [Nat.add_zero] using prefixRun 0)).1
  obtain ⟨foldedStorage, foldCounts⟩ := SourcePruningEnumerationFoldInvariants.run_preserves
    checkEmpty foldFuel foldP foldH recorded beforeCaller joined winner memos.query (.ok (some foldRaw))
    foldCaller foldQueries folded (EnumerationCanonicalUnion.mergedRoots roots recorded winner) moved
    joinedStorage prefixCounts (by simpa only [Nat.add_zero] using foldRun 0 foldP foldH (by omega) (by omega))
  have foldedRoot : IsRoot folded.representatives winner := by
    simpa only [foldForest] using joinedRoot
  rcases foldShape with rejected | completed
  · subst foldRaw
    refine ⟨prefixFuel, foldFuel, foldP, foldH, recorded, winner, moved, joined, [], foldCaller,
      folded, foldQueries, foldFinal, foldInventory, [], foldCaller, folded, foldQueries, foldFinal,
      foldInventory, prefixRun, recordedSame, winnerMember, movedSame, foldRun, .inl rfl,
      foldPost, foldQuerySame, foldedStorage, foldRealized, foldedRoot, foldCounts,
      ?_, foldPost, foldQuerySame, ?_, ?_⟩
    · intro extraRepresentative extraNative P H enoughP enoughH
      simp only [run, ite_eq_right nonempty, prefixRun extraRepresentative,
        foldRun extraNative P H enoughP enoughH]
    · intro isRejected
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro isCompleted
      cases isCompleted
  · subst foldRaw
    have foldedAvailable : Available foldCaller.checked.native.machine.heap incoming := by
      exact foldPost.effects.keeps.available incoming available
    have foldedBounded : ∀ sc ∈ incomingScs, sc.var < folded.counter := by
      intro sc member
      rw [foldCounter, show joined.counter = before.counter from
        congrArg EnumerationState.State.counter joinedSame]
      exact incomingBounded sc member
    obtain ⟨incomingR, incomingN, incomingP, incomingH, oldNode, oldScs, read, afterWrite,
      afterCaller, savedQueries, final, next, replacement, handle, reading, frame, incomingRun,
      writePrefix, afterSame, afterStored, afterStorage, afterRealized, incomingPost,
      incomingQuerySame, _, replacementAvailable, replacementClosed, encoded, decoded, optional, present⟩ :=
      SourcePruningEnumerationIncomingNode.run_complete formulas solver foldInventory foldCaller folded
        checkEmpty winner incoming incomingScs foldFinal foldPost.context foldRealized foldedStorage
        foldedRoot (foldCompleted rfl).1 foldedAvailable closed foldedBounded
        ((ranges prefixFuel recorded winner moved joined
          (by simpa only [Nat.add_zero] using prefixRun 0)).2 foldFuel foldP foldH foldCaller folded foldQueries
          (by simpa only [Nat.add_zero] using foldRun 0 foldP foldH (by omega) (by omega)))
    obtain ⟨found, lookup, oldStored, _⟩ := (getValue_success incomingR winner folded read
      (.unenumerated oldNode oldScs)).mp (by
        unfold Success
        rw [show ExceptT.run (getValue incomingR winner folded) =
            [.ok (.unenumerated oldNode oldScs, read)] from
          by simpa only [Nat.add_zero] using reading 0]
        exact List.mem_singleton_self _)
    have foundWinner : found.representative = winner := by
      obtain ⟨size, path⟩ := foldedRoot
      exact (UnionFind.reaches_unique
        (UnionFind.findRoot_correct incomingR folded.representatives winner found lookup).1 path).1
    have readStored : read.values[winner]? = some (.unenumerated oldNode oldScs) := by
      rw [frame.values, ← foundWinner]
      exact oldStored
    have readCounts : EnumerationCanonicalWaiting.Correct
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) read.values moved := by
      simpa only [frame.values] using foldCounts
    have writeCounts : EnumerationCanonicalWaiting.Correct
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) afterWrite.values
      (EnumerationCanonicalWaiting.count (EnumerationCanonicalUnion.mergedRoots roots recorded winner) 1 incomingScs moved) := by
      rw [afterSame]
      exact gained_correct read.values winner oldNode (some handle) incomingScs oldScs
        (EnumerationCanonicalUnion.mergedRoots roots recorded winner) moved readStored readCounts
    have winnerBound : winner < afterWrite.counter := by
      rw [afterStorage.aligned]
      exact (List.getElem?_eq_some_iff.mp afterStored).elim (fun inside _elementEquality => inside)
    simp only [foldQuerySame] at incomingRun optional
    refine ⟨prefixFuel + incomingR, foldFuel + incomingN, foldP + incomingP, foldH + incomingH,
      recorded, winner, moved, joined, [.ok ((), folded)], foldCaller, folded, foldQueries, foldFinal,
      foldInventory, (if replacement = .empty then [] else [.ok (.hole winner, afterWrite)]),
      afterCaller, read, savedQueries, final, next, ?_, recordedSame, winnerMember, movedSame,
      ?_, .inr rfl, foldPost, foldQuerySame, foldedStorage, foldRealized, foldedRoot, foldCounts,
      ?_, foldPost.trans incomingPost, incomingQuerySame, ?_, ?_⟩
    · intro extra
      simpa only [Nat.add_assoc] using prefixRun (incomingR + extra)
    · intro extra P H enoughP enoughH
      simpa only [Nat.add_assoc] using foldRun (incomingN + extra) P H (by omega) (by omega)
    · intro extraRepresentative extraNative P H enoughP enoughH
      simp only [run, ite_eq_right nonempty, Nat.add_assoc,
        prefixRun (incomingR + extraRepresentative),
        foldRun (incomingN + extraNative) P H (by omega) (by omega)]
      rw [Nat.add_left_comm prefixFuel incomingR extraRepresentative,
        Nat.add_left_comm foldFuel incomingN extraNative,
        incomingRun (prefixFuel + extraRepresentative) (foldFuel + extraNative) P H (by omega) (by omega)]
      by_cases empty : replacement = .empty <;> simp [empty]
    · intro isRejected
      cases isRejected
    · intro isCompleted
      refine ⟨oldNode, oldScs, read, afterWrite, replacement, handle, rfl, ?_, frame, ?_, writePrefix,
        afterStored, afterStorage, afterRealized, writeCounts, rfl, winnerBound, replacementAvailable,
        replacementClosed, encoded, decoded, optional, ?_⟩
      · intro extra
        simpa only [Nat.add_assoc, Nat.add_left_comm prefixFuel incomingR extra] using reading (prefixFuel + extra)
      · intro extraRepresentative extraNative P H enoughP enoughH
        simpa only [Nat.add_assoc, Nat.add_left_comm prefixFuel incomingR extraRepresentative,
          Nat.add_left_comm foldFuel incomingN extraNative] using
          incomingRun (prefixFuel + extraRepresentative) (foldFuel + extraNative) P H (by omega) (by omega)
      · intro requestedHandle someEq
        obtain ⟨old, query, queried, oldDecoded, nextSource, nextRoots, receipt, meaning, _⟩ := present requestedHandle someEq
        exact ⟨old, query, queried, oldDecoded, nextSource, nextRoots, receipt, meaning⟩

end MicroCFTA.SourcePruningEnumerationTerminal
