from pathlib import Path
import hashlib,json
p=Path('/tmp/mcfta-pruning-enumeration-dispatch-20261024-proposal-v3')
a=Path('/tmp/mcfta-pruning-enumeration-dispatch-20261024')
assert (a/'body-gate.json').is_file()
def frag(name,indent=0):
    text=(p/name).read_text().rstrip('\n')
    return ' '*indent+text
parts=[frag('context.lean.txt'),'']
parts += ['/-- Retain the optional node and reject its empty handle before writes. -/',frag('public-optional.lean.txt')+' :=', '''  fun state =>
    if node = some 0 then [] else
      [.ok ((), assimilated state target source (.unenumerated node (sourceScs ++ targetScs)))]''','']
parts += ['/-- Keep the reached caller and query pair outside a missing encoded action. -/',frag('public-after-query.lean.txt')+' :=',frag('definition-phase.lean.txt',2)+''' :=
    if checkEmpty then
      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
    else (.done false queried beforeCaller.fourth, queries)
  match phase.1 with
  | .done answer checkedAfter saved =>''',frag('definition-replacement.lean.txt',6)+''' := if answer then .empty else query
      (.ok ((encodeNode replacement).map (fun handle =>
          SourcePruningEnumerationAssimilation.finish source target handle sourceScs targetScs replacement)),
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge, phase.2)
  | .failed _ checkedAfter saved =>
      (.error phase.1,
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge, phase.2)''','']
parts += ['/-- Select the source branches before the actual checked query and enabled check. -/',frag('public-dispatch.lean.txt')+' :=',frag('definition-noop.lean.txt',2)+''' := fun state => [.ok ((), state)]
  if source = target then (.ok (some noop), beforeCaller, queries) else
    match before.values[source]? with
    | none => (.ok none, beforeCaller, queries)
    | some .eliminated => (.ok (some noop), beforeCaller, queries)
    | some sourceValue =>
        match before.values[target]? with
        | none => (.ok none, beforeCaller, queries)
        | some targetValue =>
            match sourceValue, targetValue with
            | .unenumerated sourceNode sourceScs, .unenumerated targetNode targetScs =>
                match sourceNode, targetNode with
                | none, node | node, none =>
                    (.ok (some (finishOptional source target node sourceScs targetScs)), beforeCaller, queries)
                | some sourceHandle, some targetHandle =>
                    match lookupNode beforeCaller.checked.native.machine.heap sourceHandle,
                        lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                    | some left, some right =>''',frag('definition-actual.lean.txt',24)+''' :=
                          SourceEqualityNativeDemand.execute nativeFuel
                            (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
                            beforeCaller.checked
                        match actual with
                        | .done query queried =>''',frag('definition-prepared.lean.txt',28)+''' :=
                              afterQuery checkEmpty p h source target sourceScs targetScs query queried beforeCaller queries
                            (prepared.1.mapError Sum.inr, prepared.2.1, prepared.2.2)
                        | other => (.error (.inl other),
                            SourceCurrentAllocatedPartialState.advance beforeCaller other.state
                              beforeCaller.fourth beforeCaller.merge, queries)
                    | _, _ => (.ok none, beforeCaller, queries)
            | _, _ => (.ok (some (failure .invalidIntersection)), beforeCaller, queries)''','']
parts += ['/-- Safe raw entries derive the same finite dispatcher and exact enumeration result. -/',frag('public-complete.lean.txt')+' := by',frag('local-optional-packet.lean.txt',2)+' := by', '''    intro sourceNode targetNode merged sourceScs targetScs sourceStored targetStored different _missing carried''',frag('local-source-inside.lean.txt',4)+''' := by
      exact (List.getElem?_eq_some_iff.mp sourceStored).elim (fun bound _storedValue => bound)''',frag('local-target-inside.lean.txt',4)+''' := by
      exact (List.getElem?_eq_some_iff.mp targetStored).elim (fun bound _storedValue => bound)''',frag('local-carried-realized.lean.txt',4)+''' := by
      intro slot node scs stored
      obtain old | fresh := List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact realized oldSlot node scs oldStored
      · cases sourceNode with
        | none =>
            simp only [Option.orElse_none] at carried
            rw [← carried, ← (UVarValue.unenumerated.inj fresh).1] at targetStored
            exact realized target node targetScs targetStored
        | some sourceHandle =>
            simp only [Option.orElse_some] at carried
            rw [← carried, ← (UVarValue.unenumerated.inj fresh).1] at sourceStored
            exact realized source node sourceScs sourceStored
    refine ⟨rfl, ?_⟩
    intro nonzero
    refine ⟨?_, ?_, ?_⟩
    · simpa only [assimilated, List.getElem?_set_ne different] using
        (List.getElem?_set_self (a := UVarValue.unenumerated merged (sourceScs ++ targetScs)) targetInside)
    · exact List.getElem?_set_self (by simpa only [List.length_set] using sourceInside)
    · intro slot node scs stored
      change ((before.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set
        source .eliminated)[slot]? = some (.unenumerated (some node) scs) at stored
      obtain old | fresh := List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact carriedRealized oldSlot node scs oldStored
      · cases fresh''',frag('local-present-packet.lean.txt',2)+' := by', '''    intro sourceHandle targetHandle sourceScs targetScs sourceStored targetStored _different''',frag('local-pair-ranges.lean.txt',4)+''' := by
      simpa only [if_neg _different, sourceStored, targetStored] using ranges
    cases checkEmpty with
    | false =>
      obtain ⟨left, leftDecoded, leftAvailable, leftClosed⟩ := realized source sourceHandle sourceScs sourceStored
      obtain ⟨right, rightDecoded, rightAvailable, rightClosed⟩ := realized target targetHandle targetScs targetStored''',frag('local-decoded-ranges.lean.txt',6)+''' := by
        simpa only [leftDecoded, rightDecoded] using pairRanges
      obtain ⟨next, query, queried, nextSource, nextRoots, receipt⟩ :=
        SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right beforeCaller.checked
          initial.ready initial.admitted leftAvailable rightAvailable leftClosed rightClosed decodedRanges memos initial.globals''',frag('local-query-probes.lean.txt',6)+''' := by
        cases receipt.actual with
        | @run traceFuel trace =>
            exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes''',frag('local-query-context.lean.txt',6)+''' := by
        exact ⟨receipt.ready, receipt.admitted,
          initial.sound.advance formulas solver queried beforeCaller.fourth beforeCaller.merge receipt.effects,
          initial.stored.grows receipt.effects.keeps, initial.covered,
          SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps beforeCaller.fourth initial.correct,
          receipt.globals, queryProbes⟩''',frag('local-query-post.lean.txt',6)+''' := by
        exact ⟨queryContext, receipt.effects, Cache.extends_refl _, (Post.refl initial).fourthRetained⟩
      obtain ⟨handle, encoded, decoded⟩ := available_readback queried.native.machine.heap query
        receipt.effects.keeps.ready.semantic.1.normal.facts.coherent receipt.available receipt.closed''',frag('local-final-realized.lean.txt',6)+''' := by
        exact realized_preserved beforeCaller.checked.native.machine.heap queried.native.machine.heap
          before before realized (EnumerationCompressionFrame.Frame.refl before) receipt.effects.keeps
      refine ⟨left, right, query, query, queried, handle,
        SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge,
        memos.query, memos, next, 0, 0, leftDecoded, rightDecoded, nextSource, nextRoots, receipt,
        ?_, queryPost, rfl, finalRealized, encoded, decoded, receipt.available, receipt.closed, receipt.meaning, ?_, ?_⟩
      · intro P H enoughP enoughH
        simp only [afterQuery, Bool.false_eq_true, ↓reduceIte, encoded, Option.map_some]
      · intro _
        exact ⟨rfl, rfl, rfl⟩
      · intro impossible
        cases impossible
    | true =>
      obtain ⟨left, right, next, query, queried, reached, answer, guardSaved, checkedAfter, saved,
        final, replacement, handle, p, h, leftDecoded, rightDecoded, nextSource, nextRoots,
        receipt, guardRun, guardChecked, stable, post, skipped, performed, sound, unfolding,
        querySame, replacementSame, available, closed, encoded, decoded, preRealized, meaning⟩ :=
        SourcePruningEnumerationEnabledEmpty.pending_enabled_complete formulas solver inventory beforeCaller
          before source target sourceHandle targetHandle sourceScs targetScs memos initial realized
          sourceStored targetStored pairRanges
      refine ⟨left, right, query, replacement, queried, handle,
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge,
        guardSaved, final, next, p, h, leftDecoded, rightDecoded, nextSource, nextRoots,
        receipt, ?_, post, querySame, preRealized, encoded, decoded, available, closed, meaning, ?_, ?_⟩
      · intro P H enoughP enoughH
        simp only [afterQuery, ↓reduceIte, stable P H enoughP enoughH,
          ← replacementSame, encoded, Option.map_some]
      · intro impossible
        cases impossible
      · intro _
        exact ⟨reached, answer, guardSaved, guardRun, guardChecked, stable, rfl, replacementSame, skipped, performed⟩
  by_cases same : source = target
  · refine ⟨0, 0, 0, (fun state => [.ok ((), state)]), beforeCaller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, realized, ?_, ?_⟩
    · intro extra P H enoughP enoughH
      simp only [dispatch, if_pos same]
    · intro noWork
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro different notEliminated
      exact False.elim (different same)
  by_cases eliminated : before.values[source]? = some .eliminated
  · refine ⟨0, 0, 0, (fun state => [.ok ((), state)]), beforeCaller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, realized, ?_, ?_⟩
    · intro extra P H enoughP enoughH
      simp only [dispatch, if_neg same, eliminated]
    · intro noWork
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro different notEliminated
      exact False.elim (notEliminated eliminated)
  rcases (slots.resolve_left same).resolve_left eliminated with
    ⟨sourceNode, targetNode, sourceScs, targetScs, sourceStored, targetStored⟩
  by_cases missing : sourceNode = none ∨ targetNode = none
  ·''',frag('local-merged.lean.txt',4)+''' := sourceNode.orElse (fun _ => targetNode)
    refine ⟨0, 0, 0, finishOptional source target merged sourceScs targetScs,
      beforeCaller, memos.query, memos, inventory, ?_, Post.refl initial, rfl, realized, ?_, ?_⟩
    · intro extra P H enoughP enoughH
      simp only [dispatch, if_neg same, sourceStored, targetStored]
      cases sourceNode with
      | none => rfl
      | some sourceHandle =>
          cases targetNode with
          | none => rfl
          | some targetHandle => cases missing <;> contradiction
    · intro noWork
      exact False.elim (noWork.elim same eliminated)
    · intro different notEliminated
      refine ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored,
        (optionalPacket sourceNode targetNode merged sourceScs targetScs sourceStored targetStored same missing rfl).1,
        (optionalPacket sourceNode targetNode merged sourceScs targetScs sourceStored targetStored same missing rfl).2, ?_, ?_⟩
      · intro _
        exact ⟨rfl, rfl, rfl, rfl⟩
      · intro leftHandle rightHandle leftSame rightSame
        rcases missing with sourceMissing | targetMissing
        · rw [sourceMissing] at leftSame
          cases leftSame
        · rw [targetMissing] at rightSame
          cases rightSame
  cases sourceNode with
  | none => exact False.elim (missing (.inl rfl))
  | some sourceHandle =>
    cases targetNode with
    | none => exact False.elim (missing (.inr rfl))
    | some targetHandle =>
      obtain ⟨left, right, query, replacement, queried, handle, afterCaller, savedQueries, final, next, p, h,
        leftDecoded, rightDecoded, nextSource, nextRoots, receipt, phaseStable, post, querySame,
        preRealized, encoded, decoded, available, closed, meaning, disabled, enabled⟩ :=
        presentPacket sourceHandle targetHandle sourceScs targetScs sourceStored targetStored same
      obtain ⟨fuel, actualDone⟩ := receipt.actual.done
      obtain ⟨emptyRaw, nonemptyRaw⟩ := SourcePruningEnumerationFinish.finish_complete
        afterCaller.checked.native.machine.heap before replacement source target sourceHandle targetHandle handle
        sourceScs targetScs post.effects.keeps.ready.semantic.1.normal.facts.coherent
        available closed encoded preRealized sourceStored targetStored (Ne.symm same)''',frag('local-empty-iff.lean.txt',6)+''' := by
        constructor
        · intro isEmpty
          simpa only [isEmpty, encodeNode, Option.some.injEq] using encoded.symm
        · intro isZero
          simpa only [isZero, lookupNode, Option.some.injEq] using decoded.symm
      refine ⟨fuel, p, h, SourcePruningEnumerationAssimilation.finish source target handle sourceScs targetScs replacement,
        afterCaller, savedQueries, final, next, ?_, post, querySame, preRealized, ?_, ?_⟩
      · intro extra P H enoughP enoughH
        simp only [dispatch, if_neg same, sourceStored, targetStored, leftDecoded, rightDecoded,
          SourceEqualityNativeDemand.done_stable fuel extra _ beforeCaller.checked queried query actualDone,
          phaseStable P H enoughP enoughH, Except.mapError]
      · intro noWork
        exact False.elim (noWork.elim same eliminated)
      · intro different notEliminated
        refine ⟨some sourceHandle, some targetHandle, some handle, sourceScs, targetScs,
          sourceStored, targetStored, ?_, ?_, ?_, ?_⟩
        · by_cases isEmpty : replacement = .empty
          · simpa only [if_pos (congrArg some (emptyIff.mp isEmpty))] using emptyRaw isEmpty
          · obtain ⟨after, raw, afterSame, targetRead, sourceRead, afterRealized⟩ := nonemptyRaw isEmpty
            subst after
            simpa only [if_neg (fun zero => isEmpty (emptyIff.mpr (Option.some.inj zero)))] using raw
        · intro nonzero
          obtain ⟨after, raw, afterSame, targetRead, sourceRead, afterRealized⟩ :=
            nonemptyRaw (fun isEmpty => nonzero (congrArg some (emptyIff.mp isEmpty)))
          subst after
          exact ⟨targetRead, sourceRead, afterRealized⟩
        · intro optional
          rcases optional with absent | absent <;> cases absent
        · intro leftHandle rightHandle leftSame rightSame
          cases Option.some.inj leftSame
          cases Option.some.inj rightSame
          exact ⟨left, right, query, replacement, queried, handle, leftDecoded, rightDecoded,
            nextSource, nextRoots, receipt, rfl, encoded, decoded, available, closed, meaning, disabled, enabled⟩''','', 'end MicroCFTA.SourcePruningEnumerationDispatch','']
source='\n'.join(parts)
contracts=json.loads((p/'contracts.json').read_text())
for name,literal in contracts.items():
    assert source.count(literal.rstrip('\n'))==1,(name,source.count(literal.rstrip('\n')))
assert len(source.splitlines())<=520
out=a/'SourcePruningEnumerationDispatch.lean'; assert not out.exists(); out.write_text(source)
print(json.dumps({'source':str(out),'lines':len(source.splitlines()),'bytes':len(source.encode()),'sha256':hashlib.sha256(source.encode()).hexdigest(),'all23contracts_exact':True}))
