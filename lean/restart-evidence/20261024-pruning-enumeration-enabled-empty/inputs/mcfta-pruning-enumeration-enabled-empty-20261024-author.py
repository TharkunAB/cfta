from pathlib import Path
p=Path('/tmp/mcfta-pruning-enumeration-enabled-empty-20261024-proposal')
a=Path('/tmp/mcfta-pruning-enumeration-enabled-empty-20261024')
assert (a/'body-gate.json').is_file()
def part(name,indent=0,attachment=''):
    return ' '*indent+(p/name).read_text().rstrip('\n')+attachment+'\n'
s=part('context.lean.txt')+'\n'+part('public-check.lean.txt',attachment=' :=')
s+=part('local-guard-result.lean.txt',2,' := SourceEndpointMemo.run query queries')
s+=part('condition-check.lean.txt',2)
s+='''    (SourceCurrentAllocatedConjunctionWorker.call p h 1000 query before memo, guardResult.2)
  else (.done false before memo, guardResult.2)

'''
s+=part('public-complete.lean.txt',attachment=' := by')
s+='''  obtain ⟨left, leftDecoded, leftAvailable, leftClosed⟩ :=
    realized source sourceHandle sourceScs sourceStored
  obtain ⟨right, rightDecoded, rightAvailable, rightClosed⟩ :=
    realized target targetHandle targetScs targetStored
'''
s+=part('local-decoded-ranges.lean.txt',2,' := by')
s+='''    simpa only [leftDecoded, rightDecoded] using ranges
  obtain ⟨next, query, queried, nextSource, nextRoots, receipt⟩ :=
    SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right beforeCaller.checked
      initial.ready initial.admitted leftAvailable rightAvailable leftClosed rightClosed decodedRanges
      memos initial.globals
'''
s+=part('local-query-probes.lean.txt',2,' := by')
s+='''    cases receipt.actual with
    | run trace =>
        exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes
'''
s+=part('case-guard-run.lean.txt',2)
s+='''  | mk reached guardSaved =>
'''
s+=part('local-guard-checked.lean.txt',4,' := by')
s+='''      simpa only [guardRun] using SourceEndpointMemoCorrect.run_checked query queried.native.machine.heap
        receipt.ready.semantic.1.normal.facts.coherent receipt.available memos.query receipt.globals.query
'''
s+=part('local-query-context.lean.txt',4,' := by')
s+='''      exact ⟨receipt.ready, receipt.admitted,
        initial.sound.advance formulas solver queried beforeCaller.fourth beforeCaller.merge receipt.effects,
        initial.stored.grows receipt.effects.keeps, initial.covered,
        SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps beforeCaller.fourth initial.correct,
        ⟨receipt.globals.unfolding, guardChecked.valid⟩, queryProbes⟩
'''
s+=part('local-query-post.lean.txt',4,' := by')
s+='''      exact ⟨queryContext, receipt.effects, Cache.extends_refl _, fun key entry found => found⟩
'''
s+=part('local-phase.lean.txt',4,' := by')
s+=part('case-reached.lean.txt',6)
s+='''      | false =>
          refine ⟨false, queried, beforeCaller.fourth, {memos with query := guardSaved}, 0, 0,
            ?_, Post.refl queryContext, ?_, ?_, ?_, receipt.available, Cache.extends_refl _, rfl⟩
          · intro P H enoughP enoughH
            simp only [check, guardRun, Bool.false_eq_true, ↓reduceIte]
          · intro notReached
            exact ⟨rfl, rfl, rfl, rfl⟩
          · intro isReached
            cases isReached
          · refine ⟨fun opened => rfl, ?_⟩
            intro impossible
            cases impossible
      | true =>
          obtain ⟨workerAnswer, workerPhysical, workerSaved, workerFinal, actualCall, actualReads,
            workerPost, workerSound, workerAvailable, workerUnfolding, workerQuerySame⟩ :=
            SourceCurrentAllocatedConjunctionCaller.finite formulas solver 1000 queryContext receipt.available
          obtain ⟨p, h, physicalStable⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete actualCall
          refine ⟨workerAnswer, advancePhysical queried workerPhysical, workerSaved, workerFinal, p, h,
            ?_, workerPost, ?_, ?_, workerSound, workerAvailable, workerUnfolding, workerQuerySame⟩
          · intro P H enoughP enoughH
            simp only [check, guardRun, ↓reduceIte]
            exact Prod.ext (SourceCurrentAllocatedConjunctionWorker.call_lift
              (physicalStable P H enoughP enoughH)) rfl
          · intro notReached
            cases notReached
          · intro isReached
            exact ⟨workerPhysical, rfl, actualCall, actualReads⟩
    obtain ⟨answer, checkedAfter, saved, final, p, h, stable, checkPost, skipped, performed,
      sound, queryAvailable, unfolding, querySame⟩ := phase
'''
s+=part('local-final-post.lean.txt',4,' := by')
s+='''      exact queryPost.trans checkPost
'''
s+=part('local-replacement-facts.lean.txt',4,' := by')
s+=part('case-answer.lean.txt',6)
s+='''      | false =>
          exact ⟨queryAvailable, receipt.closed, fun ambient term => Iff.rfl⟩
      | true =>
          refine ⟨empty_available _, rfl, ?_⟩
          intro ambient term
          constructor
          · intro accepted
            cases accepted
          · intro accepted
            exact False.elim (sound.2 rfl ambient term accepted)
    obtain ⟨replacementAvailable, replacementClosed, replacementMeaning⟩ := replacementFacts
    obtain ⟨handle, encoded, decoded⟩ := available_readback checkedAfter.native.machine.heap
      (if answer then .empty else query) finalPost.context.ready.semantic.1.normal.facts.coherent
      replacementAvailable replacementClosed
'''
s+=part('local-final-realized.lean.txt',4,' := by')
s+='''      exact realized_preserved beforeCaller.checked.native.machine.heap checkedAfter.native.machine.heap
        before before realized (EnumerationCompressionFrame.Frame.refl before) finalPost.effects.keeps
    exact ⟨left, right, next, query, queried, reached, answer, guardSaved, checkedAfter, saved,
      final, (if answer then .empty else query), handle, p, h,
      leftDecoded, rightDecoded, nextSource, nextRoots, receipt, guardRun, guardChecked, stable,
      finalPost, skipped, performed, sound, unfolding, querySame, rfl,
      replacementAvailable, replacementClosed, encoded, decoded, finalRealized,
      fun ambient term => (replacementMeaning ambient term).trans (receipt.meaning ambient term)⟩

end MicroCFTA.SourcePruningEnumerationEnabledEmpty
'''
for name,literal in __import__('json').loads((p/'contracts.json').read_text()).items():
    assert s.count(literal.rstrip('\n'))==1,name
assert len(s.splitlines())<=300
(a/'SourcePruningEnumerationEnabledEmpty.lean').write_text(s)
print(len(s.splitlines()),len(s.encode()))
