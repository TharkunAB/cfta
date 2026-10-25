from pathlib import Path
import json,hashlib,datetime
area=Path('/tmp/mcfta-pruning-enumeration-cached-terminal-20261025');owner=Path(str(area)+'-proposal')
assert (area/'body-gate.json').is_file()
contracts=json.loads((owner/'contracts.json').read_text());parts=[contracts['context.lean'],'\n/-- Derive the admitted nonempty terminal run and its logical native caches. -/\n',contracts['complete.head']]
def add(s): parts.append(s)
def head(n): parts.append(contracts[n+'.head'])
add('''  obtain ⟨prefixFuel, recorded, winner, moved, _scanned, _united, joined, prefixRun,
    _scanRun, _unionRun, _winnerRun, recordedSame, movedSame, winnerMember, rootWinner,
    prefixRoots, prefixCounts, joinedSame, joinedStorage, joinedRealized, winnerPending,
    recordedPending, _keysNodup, _keysSorted, _keysMember⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_complete beforeCaller.checked.native.machine.heap
      before.core first rest before.waiting roots paths counts safe bounded pending realized
''')
head('joinedRoot');add('''    apply (root_iff joined.representatives _ prefixRoots winner).mpr
    simp only [EnumerationCanonicalUnion.mergedRoots, rootWinner, ite_self]
''')
head('joinedFlags');add('''    simpa only [congrArg EnumerationState.State.values joinedSame] using flags
''')
head('joinedCache');add('''    ⟨joined, before.expandable, moved⟩
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
''')
head('foldRun');add('''    intro extra P H enoughP enoughH
    rw [← SourcePruningEnumerationCachedFold.erase checkEmpty (foldFuel + extra) P H
      recorded beforeCaller joinedCache winner memos.query]
    exact congrArg Prod.fst (cachedFoldRun extra P H enoughP enoughH)
''')
head('foldedRoot');add('''    simpa only [foldForest] using joinedRoot
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
        prefixRun extraRepresentative, foldRun extraNative P H enoughP enoughH, List.map_nil]
    · intro isRejected
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro isCompleted
      cases isCompleted
  · subst foldRows
''')
head('foldedAvailable');add('''      exact foldPost.effects.keeps.available incoming available
''')
head('foldedBounded');add('''      intro sc member
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
            folded.core foldQueries (by simpa only [Nat.add_zero, List.map_cons, List.map_nil] using
              foldRun 0 foldP foldH (by omega) (by omega)))
''')
head('writeWaiting');add('''      simpa only [foldWaiting] using incomingWaiting
''')
head('winnerBound');add('''      rw [afterStorage.aligned]
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
        foldRun (incomingN + extraNative) P H (by omega) (by omega), List.map_cons, List.map_nil]
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
''')
source=''.join(parts)
for n,s in contracts.items():assert source.count(s.rstrip('\n'))==1,n
assert len(source.splitlines())<=900
path=area/'SourcePruningEnumerationCachedTerminal.lean';assert not path.exists();path.write_text(source)
(area/'Public.lean').write_text('import MicroCFTA.SourcePruningEnumerationCachedTerminal\nset_option pp.deepTerms true\nset_option pp.maxSteps 1000000\n#check @MicroCFTA.SourcePruningEnumerationCachedTerminal.complete\n#print axioms MicroCFTA.SourcePruningEnumerationCachedTerminal.complete\n')
r=dict(at=datetime.datetime.now().astimezone().isoformat(),author='Root',after_body_gate=True,contracts_unchanged_exact_once=len(contracts),source_lines=len(source.splitlines()),source_sha256=hashlib.sha256(source.encode()).hexdigest(),typed_haves=8,proof_lets=1,packets=3,packet_fields=89,proof_case_groups=4,existing_named_activation=1,new_definitions=0,new_instances=0,induction=0)
(area/'root-authorship.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
