from pathlib import Path
p=Path('/tmp/mcfta-pruning-enumeration-incoming-node-20261024');o=Path(str(p)+'-proposal-v2')
assert (p/'body-gate.json').exists() and (p/'activation.json').exists()
def h(name):return (o/name).read_text().rstrip('\n')
def local(name,indent,attachment,body):
 text=h(name); first,*rest=text.split('\n');return ' '*indent+first+('' if not rest else '\n'+'\n'.join(rest))+attachment+body+'\n'
s=h('context.lean.txt')+'\n\n'+h('instance-header.lean.txt')+' where\n  pure value := [value]\n  bind values continuation := values.flatMap continuation\n\n'
s+=' /-- Write the incoming payload and inherit ancestry before Empty rejection. -/\n'.lstrip()
s+=h('finish-header.lean.txt')+''' := do
  setValue target (.unenumerated (some handle) (incomingScs ++ oldScs))
  inheritAncestry target
  match replacement with
  | .empty => reject
  | _ => pure ()

/-- Execute the incoming merge and retain the actual reached read endpoint. -/
'''
s+=h('run-header.lean.txt')+''' :=
  match UnionFind.findRoot representativeFuel before.representatives uv with
  | none => (.ok (some [.error .representativeFuel]), beforeCaller, queries, before)
  | some found =>
'''
s+=local('definition-read-state.lean.txt',6,' := ','{before with representatives := found.forest}')
s+='''      match before.values[found.representative]? with
      | none => (.ok (some [.error .invalidSlot]), beforeCaller, queries, readState)
      | some (.unenumerated oldNode oldScs) =>
          match oldNode with
          | none =>
              match encodeNode incoming with
              | none => (.ok none, beforeCaller, queries, readState)
              | some handle =>
                  (.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs incoming readState))),
                    beforeCaller, queries, readState)
          | some oldHandle =>
              match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
              | none => (.ok none, beforeCaller, queries, readState)
              | some old =>
'''
s+=local('definition-actual.lean.txt',18,' :=\n', '''                    SourceEqualityNativeDemand.execute nativeFuel
                      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                      beforeCaller.checked''')
s+='''                  match actual with
                  | .done query queried =>
'''
s+=local('definition-phase.lean.txt',22,' :=\n','''                        if checkEmpty then
                          SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (.done false queried beforeCaller.fourth, queries)''')
s+=local('definition-after-caller.lean.txt',22,' :=\n','''                        SourceCurrentAllocatedPartialState.advance beforeCaller phase.1.state phase.1.memo beforeCaller.merge''')
s+='''                      match phase.1 with
                      | .done answer checkedAfter saved =>
'''
s+=local('definition-replacement.lean.txt',26,' := ','if answer then .empty else query')
s+='''                          match encodeNode replacement with
                          | none => (.ok none, afterCaller, phase.2, readState)
                          | some handle =>
                              (.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs replacement readState))),
                                afterCaller, phase.2, readState)
                      | .failed fault checkedAfter saved =>
                          (.error (.inr (.failed fault checkedAfter saved)), afterCaller, phase.2, readState)
                  | other =>
                      (.error (.inl other), SourceCurrentAllocatedPartialState.advance
                        beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries, readState)
      | some _ => (.ok (some [.error .invalidIntersection]), beforeCaller, queries, readState)

/-- Derive the exact write prefix, raw rejection and preserved storage. -/
'''
s+=h('finish-complete-header.lean.txt')+''' := by
  obtain ⟨writtenHandle, middle, writtenEncoded, _written, middleSame, middleStored, middleRealized⟩ :=
    write_available_realized heap before replacement target (incomingScs ++ oldScs)
      coherent available closed realized inside
'''
s+=local('local-same-handle.lean.txt',2,' := by\n','    exact Option.some.inj (writtenEncoded.symm.trans encoded)')
s+='  subst writtenHandle\n  subst middle\n'
s+=local('local-finish-after.lean.txt',2,' :=\n','''    {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}''')
s+=local('local-finish-raw.lean.txt',2,' := by\n','''    cases replacement with
    | empty => simp only [↓reduceIte]; rfl
    | reference name => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | node entry edges depth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | union entry members depth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | mu entry body depthShape ordinaryShape => simp only [reduceCtorEq, ↓reduceIte]; rfl''')
s+=local('local-finish-storage.lean.txt',2,' := by\n','''    exact ⟨(set_storage before storage target _ bounded).aligned,
      storage.total, storage.forest, (set_storage before storage target _ bounded).values, storage.guards⟩''')
s+='''  exact ⟨after, rfl, raw, rfl, middleStored, afterStorage, middleRealized⟩

/-- Construct finite execution from a realized pending root and current bounds. -/
'''
s+=h('run-complete-header.lean.txt')+''' := by
  obtain ⟨oldNode, oldScs, stored⟩ := pending
  obtain ⟨size, path⟩ := root
  obtain ⟨r, found, lookup⟩ := UnionFind.findRoot_terminates path
'''
s+=local('local-representative-same.lean.txt',2,' := by\n','''    exact (UnionFind.reaches_unique
      (UnionFind.findRoot_correct r before.representatives uv found lookup).1 path).1''')
s+=local('local-lookup-more.lean.txt',2,' := by\n','''    intro extra
    exact UnionFind.findRoot_moreFuel r extra before.representatives uv found lookup''')
s+=local('local-read.lean.txt',2,' := ','{before with representatives := found.forest}')
s+=local('local-reading.lean.txt',2,' := by\n','''    intro extra
    simp [getValue, rawValue, representative, lookupMore extra, representativeSame, stored, read,
      bind, get, getThe, MonadStateOf.get, set, pure,
      StateT.bind, StateT.pure, StateT.get, StateT.set,
      ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]''')
s+=local('local-representative-run.lean.txt',2,' := by\n','''    exact (representative_success r uv before read uv).mpr
      ⟨found, lookup, representativeSame.symm, rfl⟩''')
s+=local('local-frame.lean.txt',2,' := by\n','''    exact representative_frame r uv uv before read storage.total representativeRun''')
s+=local('local-read-storage.lean.txt',2,' := by\n','''    exact representative_storage before storage r uv (by
      rw [storage.aligned]
      exact (List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)) found lookup''')
s+=local('local-read-realized.lean.txt',2,' := by\n','''    intro slot node scs currentStored
    exact realized slot node scs currentStored''')
s+=local('local-merged-bounded.lean.txt',2,' := by\n','''    intro sc member
    rcases List.mem_append.mp member with incomingMember | oldMember
    · exact bounded sc incomingMember
    · exact (storage.values (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)) sc oldMember''')
s+='''  cases oldNode with
  | none =>
    obtain ⟨handle, encoded, decoded⟩ := available_readback beforeCaller.checked.native.machine.heap incoming
      initial.ready.semantic.1.normal.facts.coherent available closed
    obtain ⟨after, writePrefix, raw, afterSame, afterStored, afterStorage, afterRealized⟩ :=
      finish_complete beforeCaller.checked.native.machine.heap read incoming uv handle incomingScs oldScs
        initial.ready.semantic.1.normal.facts.coherent available closed encoded readRealized readStorage
        ((List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)) mergedBounded
    refine ⟨r, 0, 0, 0, none, oldScs, read, after, beforeCaller, memos.query, memos, inventory, incoming, handle,
      reading, frame, ?_, writePrefix, afterSame, afterStored, afterStorage, afterRealized,
      Post.refl initial, rfl, Cache.extends_refl _, available, closed, encoded, decoded, ?_, ?_⟩
    · intro extra extraNative P H enoughP enoughH
      simp only [run, lookupMore extra, representativeSame, stored, encoded, raw]
      rfl
    · intro noneEq
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · intro requestedHandle someEq
      cases someEq
  | some oldHandle =>
    obtain ⟨old, oldDecoded, oldAvailable, oldClosed⟩ := realized uv oldHandle oldScs stored
'''
s+=local('local-decoded-ranges.lean.txt',4,' := by\n','''      simpa only [stored, oldDecoded] using ranges''')
s+='''    obtain ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle, n, p, h,
      nextSource, nextRoots, receipt, nativeStable, checkStable, actualPost, querySame, unfolding,
      _sound, replacementSame, replacementAvailable, replacementClosed, encoded, decoded, meaning, disabled, _enabled⟩ :=
      SourcePruningEnumerationIncomingQuery.complete formulas solver inventory beforeCaller incoming old checkEmpty memos
        initial available oldAvailable closed oldClosed decodedRanges
'''
s+=local('local-final-realized.lean.txt',4,' := by\n','''      exact realized_preserved beforeCaller.checked.native.machine.heap checkedAfter.native.machine.heap
        before read realized frame actualPost.effects.keeps''')
s+='''    obtain ⟨after, writePrefix, raw, afterSame, afterStored, afterStorage, afterRealized⟩ :=
      finish_complete checkedAfter.native.machine.heap read replacement uv handle incomingScs oldScs
        actualPost.effects.keeps.ready.semantic.1.normal.facts.coherent replacementAvailable replacementClosed
        encoded finalRealized readStorage
        ((List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)) mergedBounded
    refine ⟨r, n, p, h, some oldHandle, oldScs, read, after,
      SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge,
      queries, final, next, replacement, handle, reading, frame, ?_, writePrefix, afterSame, afterStored,
      afterStorage, afterRealized, actualPost, querySame, unfolding, replacementAvailable, replacementClosed,
      encoded, decoded, ?_, ?_⟩
    · intro extra extraNative P H enoughP enoughH
      simp only [run, lookupMore extra, representativeSame, stored, oldDecoded, nativeStable extraNative,
        checkStable P H enoughP enoughH, SourceCurrentAllocatedConjunctionWorker.Outcome.state,
        SourceCurrentAllocatedConjunctionWorker.Outcome.memo, ← replacementSame, encoded, raw]
      rfl
    · intro noneEq
      cases noneEq
    · intro requestedHandle someEq
      cases Option.some.inj someEq
      refine ⟨old, query, queried, oldDecoded, nextSource, nextRoots, receipt, meaning, ?_⟩
      intro disabledFlag
      obtain ⟨_answerFalse, replacementQuery, checkedSame, savedSame, _queriesSame, finalSame⟩ := disabled disabledFlag
      exact ⟨replacementQuery, by rw [checkedSame, savedSame], finalSame⟩

end MicroCFTA.SourcePruningEnumerationIncomingNode
'''
for name,t in __import__('json').loads((o/'contracts.json').read_text()).items():assert s.count(t.rstrip('\n'))==1,name
assert len(s.splitlines())<=560
(p/'candidate.lean').write_text(s)
print('Root-authored candidate',len(s.splitlines()),len(s.encode()))
