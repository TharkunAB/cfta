from pathlib import Path
import json

area = Path('/tmp/mcfta-pruning-enumeration-fold-20261024')
owner = Path(str(area) + '-proposal-v2')
contracts = json.loads((owner / 'contracts.json').read_text())
parts = []

def emit(text):
    parts.append(text)

def fragment(name, indent=0, attachment=' := by\n'):
    literal = contracts[name].rstrip('\n')
    emit(' ' * indent + literal + attachment)

emit(contracts['context.lean.txt'] + '\n')
emit('/-- Run the recorded source slots in order and retain each reached state. -/\n')
fragment('run-header.lean.txt', attachment=' :=\n')
emit('''  match sources with
  | [] => (.ok (some [.ok ((), before)]), beforeCaller, queries, before)
  | source :: rest =>
''')
fragment('definition-observation.lean.txt', 4, ' :=\n      SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h beforeCaller before source target queries\n')
emit('''    match observation with
    | (.error fault, reachedCaller, savedQueries) => (.error fault, reachedCaller, savedQueries, before)
    | (.ok none, reachedCaller, savedQueries) => (.ok none, reachedCaller, savedQueries, before)
    | (.ok (some action), reachedCaller, savedQueries) =>
''')
fragment('definition-raw.lean.txt', 8, ' := ExceptT.run (action before)\n')
emit('''        match raw with
        | [.ok ((), after)] => run checkEmpty nativeFuel p h rest reachedCaller after target savedQueries
        | other => (.ok (some other), reachedCaller, savedQueries, before)

/-- Every reached decoded request fits the fixed machine width. -/
''')
fragment('ranges-header.lean.txt', attachment=' :=\n')
emit('''  match sources with
  | [] => True
  | source :: rest =>
      (if source = target then True else
        match before.values[source]?, before.values[target]? with
        | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
            match lookupNode beforeCaller.checked.native.machine.heap left,
                lookupNode beforeCaller.checked.native.machine.heap right with
            | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
                beforeCaller.checked
            | _, _ => True
        | _, _ => True) ∧
      ∀ nativeFuel p h action afterCaller saved after,
        SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
          beforeCaller before source target queries = (.ok (some action), afterCaller, saved) →
        ExceptT.run (action before) = [.ok ((), after)] →
        Ranges checkEmpty rest afterCaller after target saved

/-- Safe pending slots derive either the complete fold or its first rejection. -/
''')
fragment('complete-header.lean.txt')
emit('''  induction sources generalizing inventory beforeCaller before memos with
  | nil =>
    refine ⟨0, 0, 0, [.ok ((), before)], beforeCaller, before, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, realized, .inr rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro extra P H _largeP _largeH
      rfl
    · intro _completed
      exact ⟨targetPending, by simp⟩
    · intro slot oldEliminated
      exact oldEliminated
    · intro slot _different
      rfl
    · intro rejected
      cases rejected
  | cons source rest ih =>
''')
fragment('local-head-ranges.lean.txt', 4)
emit('''      exact ranges.1
''')
fragment('local-head-packet.lean.txt', 4)
emit('''      obtain ⟨targetNode, targetScs, targetPendingStored⟩ := targetPending
''')
fragment('local-source-selected.lean.txt', 6)
emit('''        exact selected source (by simp)
''')
fragment('local-slots.lean.txt', 6)
emit('''        rcases sourceSelected with storedEliminated | ⟨sourceNode, sourceScs, sourcePendingStored⟩
        · exact .inr (.inl storedEliminated)
        · exact .inr (.inr ⟨sourceNode, targetNode, sourceScs, targetScs, sourcePendingStored, targetPendingStored⟩)
      obtain ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, dispatchQueries, dispatchMemos,
        dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame, unchangedRealized,
        noopOutcome, changedOutcome⟩ := SourcePruningEnumerationDispatch.dispatch_complete
          formulas solver inventory beforeCaller before checkEmpty source target memos initial realized slots headRanges
      by_cases same : source = target
      · refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, before, dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          unchangedRealized, .inr (noopOutcome (.inl same)).1, ?_, ⟨targetNode, targetScs, targetPendingStored⟩,
          ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro _rejected
          rfl
        · intro remaining member
          exact selected remaining (by simp [member])
        · intro different _completed
          exact False.elim (different same)
        · intro slot oldEliminated
          exact oldEliminated
        · intro slot _different
          rfl
      by_cases eliminated : before.values[source]? = some .eliminated
      · refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, before, dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          unchangedRealized, .inr (noopOutcome (.inr eliminated)).1, ?_, ⟨targetNode, targetScs, targetPendingStored⟩,
          ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro _rejected
          rfl
        · intro remaining member
          exact selected remaining (by simp [member])
        · intro _different _completed
          exact eliminated
        · intro slot oldEliminated
          exact oldEliminated
        · intro slot _different
          rfl
      obtain ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored,
        actionRaw, surviving, _optionalOutcome, _presentOutcome⟩ := changedOutcome same eliminated
      by_cases empty : merged = some 0
      · refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, before, dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          unchangedRealized, .inl (by simpa only [ite_eq_left empty] using actionRaw), ?_,
          ⟨targetNode, targetScs, targetStored⟩, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro _rejected
          rfl
        · intro remaining member
          exact selected remaining (by simp [member])
        · intro _different completed
          rw [actionRaw, ite_eq_left empty] at completed
          cases completed
        · intro slot oldEliminated
          exact oldEliminated
        · intro slot _different
          rfl
      · obtain ⟨targetAfterStored, sourceAfterStored, changedRealized⟩ := surviving empty
''')
fragment('local-changed-frame.lean.txt', 8)
emit('''          constructor
          · intro slot oldEliminated
            by_cases atTarget : slot = target
            · subst slot
              rw [targetStored] at oldEliminated
              cases oldEliminated
            by_cases atSource : slot = source
            · subst slot
              exact sourceAfterStored
            simpa only [assimilated, List.getElem?_set_ne (Ne.symm atSource),
              List.getElem?_set_ne (Ne.symm atTarget)] using oldEliminated
          · intro remaining member
            by_cases remainingTarget : remaining = target
            · subst remaining
              exact .inr ⟨merged, sourceScs ++ targetScs, targetAfterStored⟩
            by_cases remainingSource : remaining = source
            · subst remaining
              exact .inl sourceAfterStored
            rcases selected remaining (by simp [member]) with oldEliminated | ⟨oldNode, oldScs, oldPending⟩
            · exact .inl (by simpa only [assimilated, List.getElem?_set_ne (Ne.symm remainingSource),
                List.getElem?_set_ne (Ne.symm remainingTarget)] using oldEliminated)
            · exact .inr ⟨oldNode, oldScs, by
                simpa only [assimilated, List.getElem?_set_ne (Ne.symm remainingSource),
                  List.getElem?_set_ne (Ne.symm remainingTarget)] using oldPending⟩
        refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller,
          assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)), dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          changedRealized, .inr (by simpa only [ite_eq_right empty] using actionRaw), ?_,
          ⟨merged, sourceScs ++ targetScs, targetAfterStored⟩, changedFrame.2, ?_, changedFrame.1,
          ?_, rfl, rfl, rfl, rfl, ?_⟩
        · intro rejected
          rw [actionRaw, ite_eq_right empty] at rejected
          cases rejected
        · intro _different _completed
          exact sourceAfterStored
        · simp only [assimilated, List.length_set]
        · intro slot different
          simp only [assimilated, ite_eq_right different]
    obtain ⟨headFuel, headP, headH, action, headCaller, headAfter, headQueries, headMemos, headInventory,
      headRun, headPost, headQuerySame, headRealized, headShape, headRejectedSame, headTarget, headSelected,
      headSource, headEliminated, headLength, headRepresentatives, headCounter, headObligations,
      headExpansion, headAncestry⟩ := headPacket
    rcases headShape with headRejected | headCompleted
    · obtain rfl := headRejectedSame headRejected
      refine ⟨headFuel, headP, headH, [], headCaller, before, headQueries, headMemos, headInventory,
        ?_, headPost, headQuerySame, headRealized, .inl rfl, ?_, headEliminated,
        headLength, headRepresentatives, headCounter, headObligations, headExpansion, headAncestry, ?_⟩
      · intro extra P H largeP largeH
        simp only [run, headRun extra P H largeP largeH, headRejected]
      · intro completed
        cases completed
      · intro _rejected
        exact ⟨[], source, rest, beforeCaller, before, memos.query, action,
          rfl, by intros; rfl, headRun, headRejected, rfl⟩
    ·
''')
fragment('local-tail-ranges.lean.txt', 6)
emit('''        simpa only [headQuerySame, Nat.add_zero] using
          ranges.2 headFuel headP headH action headCaller headQueries headAfter
            (headRun 0 headP headH (Nat.le_refl _) (Nat.le_refl _)) headCompleted
      obtain ⟨tailFuel, tailP, tailH, tailRaw, tailCaller, tailAfter, tailQueries, tailMemos, tailInventory,
        tailRun, tailPost, tailQuerySame, tailRealized, tailShape, tailCompleted, tailEliminated,
        tailLength, tailRepresentatives, tailCounter, tailObligations, tailExpansion, tailAncestry,
        tailRejection⟩ := ih headInventory headCaller headAfter headMemos headPost.context
          headRealized headTarget headSelected tailRanges
''')
fragment('local-head-at.lean.txt', 6)
emit('''        intro extra P H largeP largeH
        simpa only [Nat.add_assoc] using headRun (tailFuel + extra) P H
          (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
''')
fragment('local-tail-at.lean.txt', 6)
emit('''        intro extra P H largeP largeH
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tailRun (headFuel + extra) P H
          (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
      refine ⟨headFuel + tailFuel, max headP tailP, max headH tailH, tailRaw, tailCaller, tailAfter,
        tailQueries, tailMemos, tailInventory, ?_, headPost.trans tailPost, tailQuerySame,
        tailRealized, tailShape, ?_, ?_, tailLength.trans headLength, tailRepresentatives.trans headRepresentatives,
        tailCounter.trans headCounter, tailObligations.trans headObligations, tailExpansion.trans headExpansion,
        ?_, ?_⟩
      · intro extra P H largeP largeH
        rw [run, headAt extra P H largeP largeH, headCompleted]
        rw [← headQuerySame]
        exact tailAt extra P H largeP largeH
      · intro completed
        refine ⟨(tailCompleted completed).1, ?_⟩
        intro remaining member different
        rcases List.mem_cons.mp member with memberHead | memberRest
        · subst remaining
          exact tailEliminated source (headSource different headCompleted)
        · exact (tailCompleted completed).2 remaining memberRest different
      · intro slot oldEliminated
        exact tailEliminated slot (headEliminated slot oldEliminated)
      · intro slot different
        exact (tailAncestry slot different).trans (headAncestry slot different)
      · intro rejected
        obtain ⟨«prefix», rejectSource, suffix, prefixCaller, prefixEnum, prefixQueries, rejectAction,
          split, prefixRun, rejectRun, rejectRaw, rejectedAfter⟩ := tailRejection rejected
        refine ⟨source :: «prefix», rejectSource, suffix, prefixCaller, prefixEnum, prefixQueries, rejectAction,
          ?_, ?_, ?_, rejectRaw, rejectedAfter⟩
        · simp only [List.cons_append, split]
        · intro extra P H largeP largeH
          rw [run, headAt extra P H largeP largeH, headCompleted]
          rw [← headQuerySame]
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixRun (headFuel + extra) P H
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
        · intro extra P H largeP largeH
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rejectRun (headFuel + extra) P H
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)

end MicroCFTA.SourcePruningEnumerationFold
''')
source = ''.join(parts)
for name, literal in contracts.items():
    assert source.count(literal.rstrip('\n')) == 1, name
assert len(source.splitlines()) <= 600
(area / 'SourcePruningEnumerationFold.lean').write_text(source)
print(len(source.splitlines()), len(source.encode()))
