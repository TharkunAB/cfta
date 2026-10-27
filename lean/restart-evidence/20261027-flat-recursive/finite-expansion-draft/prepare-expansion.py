from pathlib import Path
import re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
area=Path('/tmp/mcfta-flat-recursive-20261027/finite-expansion-draft')
s=(root/'SourcePruningEnumerationFiniteExpansionResources.lean').read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationFiniteParkedResources','import MicroCFTA.SourceFlatPruningRecursiveParkedResources')
s=s.replace('import MicroCFTA.SourcePruningEnumerationFiniteOrdinaryForecastResources','import MicroCFTA.SourceFlatPruningRecursiveOrdinaryForecastResources')
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationRecursive','namespace MicroCFTA.SourceFlatPruningRecursive').replace('end MicroCFTA.SourcePruningEnumerationRecursive','end MicroCFTA.SourceFlatPruningRecursive')
s=s.replace('open SourcePruningEnumerationSelectedStep (runPrefix)','open SourcePruningEnumerationSelectedStep (runPrefix)\nopen SourcePruningEnumerationRecursive (Packet OutcomeResources)')
for ident in ['resume','finish','continueWith','Output','Failure','resume_depth_stable']:
 s=re.sub(r'(?<![A-Za-z0-9_.])'+ident+r'\b','SourcePruningEnumerationRecursive.'+ident,s)
s=s.replace('SourcePruningEnumerationNativeOrdinaryContinuations.ordinary_finite_complete_forecast','SourceFlatPruningNativeOrdinaryContinuations.ordinary_finite_complete_forecast')
s=s.replace('        (Forecast (recursiveFuel + 1) seed ceiling) outcome := by','''        (Forecast (recursiveFuel + 1) seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) (recursiveFuel + 1) metadata caller memos.query flat (some (.expand uv)) = flatOutcome ∧
          ResultRelated flatOutcome outcome := by''')
s=s.replace('⟨bound, outcome, running, resources⟩ := parked_finite_complete_resources','⟨bound, outcome, running, resources, flatRunning⟩ := parked_finite_complete_resources')
s=s.replace('simpa only [SourcePruningEnumerationFiniteReservation.final_succ] using resources⟩','simpa only [SourcePruningEnumerationFiniteReservation.final_succ] using resources, flatRunning⟩',1)
old='''    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, certificate.mono
      stageGrowth.1 stageGrowth.2⟩
    intro extra
    rw [SourcePruningEnumerationRecursive.resume, (phase extra).1]'''
new='''    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, certificate.mono
      stageGrowth.1 stageGrowth.2, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationRecursive.resume, (phase extra).1]
    · intro flat related extra
      have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
        holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
        (prefixFuel + extra) uv caller before flat memos related (phase extra).2
      rw [(phase extra).1] at replay
      obtain ⟨flatChecked, flatPrepared, observed⟩ :=
        SourceFlatPruningRecursivePrefixShape.rejected _ checked _ reached memos.query replay
      refine ⟨.complete [] reached memos.query, ?_, .nil, rfl, rfl⟩
      rw [resume, observed]'''
assert old in s
s=s.replace(old,new)
s=s.replace('_finalFits, _finalKnown, certificate⟩ :=','_finalFits, _finalKnown, certificate, flatRunning⟩ :=')
old='''      refine ⟨prefixFuel + scanFuel, SourcePruningEnumerationRecursive.finish uv result, ?_, certificate.post middlePost⟩
      apply SourcePruningEnumerationRecursive.resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
        prefixFuel scanFuel recursiveFuel uv metadata metadata caller reached memos.query memos.query before after
        [.ok ((uv, handle, scs, .node entry rows depth free), entered.core)] result
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
        exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
      · intro extra
        simpa only [middleQuery] using outerRun extra'''
new='''      refine ⟨prefixFuel + scanFuel, SourcePruningEnumerationRecursive.finish uv result, ?_,
        certificate.post middlePost, ?_⟩
      · apply SourcePruningEnumerationRecursive.resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
          prefixFuel scanFuel recursiveFuel uv metadata metadata caller reached memos.query memos.query before after
          [.ok ((uv, handle, scs, .node entry rows depth free), entered.core)] result
        · intro extra
          obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
          exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
        · intro extra
          simpa only [middleQuery] using outerRun extra
      · intro flat related extra
        let w := prefixFuel + scanFuel + extra
        obtain ⟨currentAction, currentPrefix, currentValid⟩ := phase (scanFuel + extra)
        have prefixSame : prefixFuel + (scanFuel + extra) = w := by dsimp [w]; omega
        rw [prefixSame] at currentPrefix currentValid
        have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
          holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
          w uv caller before flat memos related currentValid
        rw [currentPrefix] at replay
        obtain ⟨flatChecked, flatPrepared, actionCore, flatAfter, rightCore, observed, caches⟩ :=
          SourceFlatPruningRecursivePrefixShape.accepted _ checked _ reached memos.query after metadata replay
        obtain ⟨flatEntered, flatResult, actual, _enteredRelated, foldedRelated⟩ :=
          flatRunning flatAfter caches (prefixFuel + extra)
        have scanSame : scanFuel + (prefixFuel + extra) = w := by dsimp [w]; omega
        rw [scanSame, middleQuery] at actual
        refine ⟨finish uv flatResult, ?_, finish_related uv flatResult result foldedRelated⟩
        change resume holeKey fits admits graph templates checkEmpty edgesOf stop order w (recursiveFuel + 1)
          metadata caller memos.query flat (some (.expand uv)) = finish uv flatResult
        rw [resume, observed]
        dsimp only
        rw [actual]'''
assert old in s
s=s.replace(old,new)
old='''      refine ⟨prefixFuel + entryFuel, outcome, ?_, (certificate.mono
        stageGrowth.1 stageGrowth.2).post middlePost⟩
      intro extra
      obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
      have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [samePrefix] at currentPrefix
      have actual := fallbackRun (prefixFuel + extra)
        (SourcePruningEnumerationRecursive.continueWith (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + entryFuel + extra) recursiveFuel) graph templates stop order
          (prefixFuel + entryFuel + extra) metadata uv)
      have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [sameEntry, middleQuery] at actual
      rw [SourcePruningEnumerationRecursive.resume, currentPrefix]
      dsimp only
      rw [actual]'''
new='''      refine ⟨prefixFuel + entryFuel, outcome, ?_, (certificate.mono
        stageGrowth.1 stageGrowth.2).post middlePost, ?_⟩
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
        have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [samePrefix] at currentPrefix
        have actual := fallbackRun (prefixFuel + extra)
          (SourcePruningEnumerationRecursive.continueWith (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (prefixFuel + entryFuel + extra) recursiveFuel) graph templates stop order
            (prefixFuel + entryFuel + extra) metadata uv)
        have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [sameEntry, middleQuery] at actual
        rw [SourcePruningEnumerationRecursive.resume, currentPrefix]
        dsimp only
        rw [actual]
      · intro flat related extra
        let w := prefixFuel + entryFuel + extra
        obtain ⟨currentAction, currentPrefix, currentValid⟩ := phase (entryFuel + extra)
        have samePrefix : prefixFuel + (entryFuel + extra) = w := by dsimp [w]; omega
        rw [samePrefix] at currentPrefix currentValid
        have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
          holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
          w uv caller before flat memos related currentValid
        rw [currentPrefix] at replay
        obtain ⟨flatChecked, flatPrepared, actionCore, flatAfter, rightCore, observed, caches⟩ :=
          SourceFlatPruningRecursivePrefixShape.accepted _ checked _ reached memos.query after metadata replay
        have oldEntry := _entryRun (prefixFuel + extra)
        have sameEntry : entryFuel + (prefixFuel + extra) = w := by dsimp [w]; omega
        rw [sameEntry] at oldEntry
        obtain ⟨flatEntered, flatEntry, enteredRelated⟩ := SourceFlatPruningEntry.enter_replays
          reached.checked.native.machine.heap w uv flatAfter.core after.core
          (uv, handle, scs, value) entered.core caches.core oldEntry
        have flatFallback : ∀ hook, SourceFlatPruningNativeOrdinaryContinuations.run hook
            checkEmpty w w w uv edgesOf reached flatAfter memos.query =
              ([.ok ((uv, handle, scs, value), flatEntered)], none) := by
          intro hook
          unfold SourceFlatPruningNativeOrdinaryContinuations.run
          rw [flatEntry]
          cases value with
          | node entry edges depth free => simp only [fallback, ↓reduceIte]
          | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => rfl
        let flatRaw := [Except.ok (ε := EnumerationState.Error) ((uv, handle, scs, value), flatEntered)]
        let flatOutcome := SourcePruningEnumerationNativeContinuations.HookResult.stopped
          (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          [] (.ordinary uv flatRaw) (some (reached, memos.query))
        refine ⟨flatOutcome, ?_, .nil, .ordinary uv (.cons (.ok _ enteredRelated) .nil), rfl⟩
        change resume holeKey fits admits graph templates checkEmpty edgesOf stop order w (recursiveFuel + 1)
          metadata caller memos.query flat (some (.expand uv)) = flatOutcome
        rw [resume, observed]
        dsimp only
        rw [flatFallback]'''
assert old in s
s=s.replace(old,new)
s=s.replace('# A positive finite recursive depth under an original reservation','# Actual flat selected expansion at a positive finite depth')
s=s.replace('The original packet supplies the selected prefix and its actual continuation.','The original packet supplies one uniform prefix before the flat input is chosen.\nEvery related flat cache executes that prefix at the same work bound.')
(area/'SourceFlatPruningRecursiveExpansionResources.lean').write_text(s)
