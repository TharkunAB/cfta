from pathlib import Path
import hashlib,json
area=Path('/tmp/mcfta-pruning-enumeration-terminal-20261024')
owner=Path(str(area)+'-proposal')
assert json.loads((area/'body-gate.json').read_text())['status']=='ACCEPTED_BEFORE_ANY_BODY_OR_ACTIVATION'
def literal(name):return (owner/name).read_text().rstrip('\n')
def local(name,indent):return ' '*indent+literal(name)+' := by\n'
source=literal('context.lean.txt')+'\n\n'+literal('instance-header.lean.txt')+''' where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Run the terminal prefix, ordered fold and actual incoming merge. -/
'''+literal('run-header.lean.txt')+''' :=
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
'''+literal('gained-header.lean.txt')+' := by\n'+local('gained-same.lean.txt',2)+'''    funext key
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
'''+literal('complete-header.lean.txt')+''' := by
  obtain ⟨prefixFuel, recorded, winner, moved, _, _, joined, prefixRun, _, _, _, recordedSame,
    movedSame, winnerMember, rootWinner, prefixRoots, prefixCounts, joinedSame, joinedStorage,
    joinedRealized, winnerPending, recordedPending, _, _, _⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_complete beforeCaller.checked.native.machine.heap before
      first rest waiting roots paths counts safe bounded pending realized
'''+local('local-joined-root.lean.txt',2)+'''    apply (root_iff joined.representatives _ prefixRoots winner).mpr
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
'''+local('local-folded-root.lean.txt',2)+'''    simpa only [foldForest] using joinedRoot
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
'''+local('local-folded-available.lean.txt',4)+'''      exact foldPost.effects.keeps.available incoming available
'''+local('local-folded-bounded.lean.txt',4)+'''      intro sc member
      simpa only [foldCounter, joinedSame] using incomingBounded sc member
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
'''+local('local-found-winner.lean.txt',4)+'''      obtain ⟨size, path⟩ := foldedRoot
      exact (UnionFind.reaches_unique
        (UnionFind.findRoot_correct incomingR folded.representatives winner found lookup).1 path).1
'''+local('local-read-stored.lean.txt',4)+'''      rw [frame.values, ← foundWinner]
      exact oldStored
'''+local('local-read-counts.lean.txt',4)+'''      simpa only [frame.values] using foldCounts
'''+local('local-write-counts.lean.txt',4)+'''      rw [afterSame]
      exact gained_correct read.values winner oldNode (some handle) incomingScs oldScs
        (EnumerationCanonicalUnion.mergedRoots roots recorded winner) moved readStored readCounts
'''+local('local-winner-bound.lean.txt',4)+'''      rw [afterStorage.aligned]
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
'''
assert len(source.splitlines())<=650
contracts=json.loads((owner/'contracts.json').read_text())
for n,s in contracts.items():assert source.count(s.rstrip('\n'))==1,n
(area/'SourcePruningEnumerationTerminal.lean').write_text(source)
print(json.dumps({'lines':len(source.splitlines()),'bytes':len(source.encode()),'sha256':hashlib.sha256(source.encode()).hexdigest(),'contracts':len(contracts)}))
