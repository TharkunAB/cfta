from pathlib import Path
area=Path('/tmp/mcfta-pruning-enumeration-incoming-20261024')
p=Path(str(area)+'-proposal')
def have(name,indent,body):
    return ' '*indent+(p/f'local-{name}.lean.txt').read_text().rstrip('\n')+' := by\n'+body
source=(p/'context.lean.txt').read_text()+ '/-- Construct one checked intersection and its optional sound Empty replacement. -/\n'+(p/'complete-header.lean.txt').read_text().rstrip('\n')+' := by\n'
source+='''  obtain ⟨next, query, queried, nextSource, nextRoots, receipt⟩ :=
    SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right beforeCaller.checked
      initial.ready initial.admitted leftAvailable rightAvailable leftClosed rightClosed ranges memos initial.globals
  obtain ⟨fuel, nativeDone⟩ := receipt.actual.done
'''
source+=have('query-probes',2,'''    cases receipt.actual with
    | @run traceFuel trace =>
        exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes
''')
source+=have('query-context',2,'''    exact ⟨receipt.ready, receipt.admitted,
      initial.sound.advance formulas solver queried beforeCaller.fourth beforeCaller.merge receipt.effects,
      initial.stored.grows receipt.effects.keeps, initial.covered,
      SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps beforeCaller.fourth initial.correct,
      receipt.globals, queryProbes⟩
''')
source+=have('query-post',2,'''    exact ⟨queryContext, receipt.effects, Cache.extends_refl _, fun key entry found => found⟩
''')
source+='''  cases checkEmpty with
  | false =>
      obtain ⟨handle, encoded, decoded⟩ := available_readback queried.native.machine.heap query
        receipt.effects.keeps.ready.semantic.1.normal.facts.coherent receipt.available receipt.closed
      refine ⟨next, query, queried, false, queried, beforeCaller.fourth, memos, memos.query,
        query, handle, fuel, 0, 0, nextSource, nextRoots, receipt, ?_, ?_, queryPost, rfl,
        Cache.extends_refl _, ?_, rfl, receipt.available, receipt.closed, encoded, decoded,
        receipt.meaning, ?_, ?_⟩
      · intro extra
        exact SourceEqualityNativeDemand.done_stable fuel extra _ beforeCaller.checked queried query nativeDone
      · intro P H enoughP enoughH
        simp only [Bool.false_eq_true, ↓reduceIte]
      · refine ⟨fun opened => rfl, ?_⟩
        intro impossible
        cases impossible
      · intro disabled
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro enabled
        cases enabled
  | true =>
    cases guardRun : SourceEndpointMemo.run query memos.query with
    | mk reached guardSaved =>
'''
source+=have('guard-checked',6,'''        simpa only [guardRun] using SourceEndpointMemoCorrect.run_checked query queried.native.machine.heap
          receipt.effects.keeps.ready.semantic.1.normal.facts.coherent receipt.available memos.query receipt.globals.query
''')
source+=have('guard-context',6,'''        exact ⟨queryContext.ready, queryContext.admitted, queryContext.sound, queryContext.stored,
          queryContext.covered, queryContext.correct,
          ⟨receipt.globals.unfolding, guardChecked.valid⟩, queryContext.probes⟩
''')
source+=have('guard-post',6,'''        exact ⟨guardContext, receipt.effects, Cache.extends_refl _, fun key entry found => found⟩
''')
source+=have('phase',6,'''        cases reached with
        | false =>
            refine ⟨false, queried, beforeCaller.fourth, {memos with query := guardSaved}, 0, 0,
              ?_, Post.refl guardContext, ?_, ?_, ?_, receipt.available, Cache.extends_refl _, rfl⟩
            · intro P H enoughP enoughH
              simp only [SourcePruningEnumerationEnabledEmpty.check, guardRun, Bool.false_eq_true, ↓reduceIte]
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
              SourceCurrentAllocatedConjunctionCaller.finite formulas solver 1000 guardContext receipt.available
            obtain ⟨p, h, physicalStable⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete actualCall
            refine ⟨workerAnswer, advancePhysical queried workerPhysical, workerSaved, workerFinal, p, h,
              ?_, workerPost, ?_, ?_, workerSound, workerAvailable, workerUnfolding, workerQuerySame⟩
            · intro P H enoughP enoughH
              simp only [SourcePruningEnumerationEnabledEmpty.check, guardRun, ↓reduceIte]
              exact Prod.ext (SourceCurrentAllocatedConjunctionWorker.call_lift
                (physicalStable P H enoughP enoughH)) rfl
            · intro notReached
              cases notReached
            · intro isReached
              exact ⟨workerPhysical, rfl, actualCall, actualReads⟩
''')
source+='''      obtain ⟨answer, checkedAfter, saved, final, p, h, stable, checkPost, skipped, performed,
        sound, queryAvailable, unfolding, querySame⟩ := phase
'''
source+=have('final-post',6,'''        exact guardPost.trans checkPost
''')
source+=have('replacement-facts',6,'''        cases answer with
        | false =>
            exact ⟨queryAvailable, receipt.closed, fun ambient term => Iff.rfl⟩
        | true =>
            refine ⟨empty_available _, rfl, ?_⟩
            intro ambient term
            constructor
            · intro accepted
              simp only [↓reduceIte, InternedGuardedLanguage.meaning] at accepted
            · intro accepted
              exact False.elim (sound.2 rfl ambient term accepted)
''')
source+='''      obtain ⟨replacementAvailable, replacementClosed, replacementMeaning⟩ := replacementFacts
      obtain ⟨handle, encoded, decoded⟩ := available_readback checkedAfter.native.machine.heap
        (if answer then .empty else query) finalPost.effects.keeps.ready.semantic.1.normal.facts.coherent
        replacementAvailable replacementClosed
      refine ⟨next, query, queried, answer, checkedAfter, saved, final, guardSaved,
        (if answer then .empty else query), handle, fuel, p, h, nextSource, nextRoots, receipt,
        ?_, ?_, finalPost, querySame, unfolding, sound, rfl, replacementAvailable,
        replacementClosed, encoded, decoded, ?_, ?_, ?_⟩
      · intro extra
        exact SourceEqualityNativeDemand.done_stable fuel extra _ beforeCaller.checked queried query nativeDone
      · intro P H enoughP enoughH
        simpa only [↓reduceIte] using stable P H enoughP enoughH
      · intro ambient term
        exact (replacementMeaning ambient term).trans (receipt.meaning ambient term)
      · intro disabled
        cases disabled
      · intro enabled
        exact ⟨reached, guardRun, guardChecked, skipped, performed⟩

end MicroCFTA.SourcePruningEnumerationIncomingQuery
'''
for name,literal in __import__('json').loads((p/'contracts.json').read_text()).items():assert source.count(literal.rstrip('\n'))==1,name
assert len(source.splitlines())<=340
out=area/'candidate/MicroCFTA/SourcePruningEnumerationIncomingQuery.lean';out.parent.mkdir(parents=True);out.write_text(source)
print(len(source.splitlines()),'lines',len(source.encode()),'bytes',__import__('hashlib').sha256(source.encode()).hexdigest())
