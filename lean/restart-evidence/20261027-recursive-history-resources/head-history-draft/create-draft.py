from pathlib import Path
out=Path('/tmp/mcfta-recursive-history-resources-20261027/head-history-draft')
source=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationCallbackAdmission.lean').read_text()
ctx=source[source.index('namespace MicroCFTA.SourcePruningEnumerationNativeHookResources'):source.index('/-- Keep the full actual head packet')]
ctx=ctx.replace('open EnumerationState EnumerationSchedule','open EnumerationState EnumerationCorrectness EnumerationSchedule',1)
ctx=ctx.replace('local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint','local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint\nlocal notation "Core" => EnumerationState.State Symbol Constraint',1)
ctx=ctx.replace('open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume Complete OutcomeResources)','open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume CompleteWithHistory OutcomeResources)',1)
ctx+='local notation "CallbackResult" => HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)\n\n'
header=source[source.index('theorem head_finite_complete_resources_with_callback_admission'):]
header=header[:header.index(' := by')]
header=header.replace('head_finite_complete_resources_with_callback_admission','head_finite_complete_resources_with_history',1).replace('(recursive : Complete (bits := bits)','(recursive : CompleteWithHistory (bits := bits)',1)
header=header.replace('''          match outcome with''','''          (match outcome with''',1)
append='''          | .stopped _ _ _ => True) ∧
          (match (generalizing := false) receipt with
          | .complete fragment actual queries after =>
              ∃ (result : Bool × SourcePruningRecordTypes.Metadata Typing) (callbackCore : Core),
                (∀ extra,
                  Success (SourcePruningRecordTypes.recordTypes graph templates (bound + extra) metadata uv
                    (.inl fragment)) after.core result callbackCore ∧
                  ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (bound + extra) metadata uv
                    (.inl fragment) after.core) = [.ok (result, callbackCore)] ∧
                  ∀ (recur : SourcePruningRecordTypes.Metadata Typing → Caller (bits + 2) → Queries → Cached →
                    Option Next → CallbackResult) stop order,
                    continueWith recur graph templates stop order (bound + extra) metadata uv fragment actual
                      middleMemos.query after =
                      if result.1 then .complete [] actual middleMemos.query
                      else recur result.2 actual middleMemos.query (EnumerationExpandableIndex.frame callbackCore after)
                        (SourcePruningEnumerationRestart.decision stop order result.2
                          (EnumerationExpandableIndex.frame callbackCore after))) ∧
                SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver middleInventory
                  actual middleMemos result.2 (EnumerationExpandableIndex.frame callbackCore after)
                  uv fragment recursiveFuel (afterHead seed inherited) (massCeil seed capturedMass inherited) ∧
                (∀ extra, result.1 = false →
                  ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
                    SourcePruningEnumerationRecursive.ResourceHistory holeKey fits admits graph templates checkEmpty
                      edgesOf stop order formulas solver (bound + extra) recursiveFuel middleInventory actual middleMemos
                      result.2 (EnumerationExpandableIndex.frame callbackCore after)
                      (afterHead seed inherited) (massCeil seed capturedMass inherited)
                      (SourcePruningEnumerationRestart.decision stop order result.2
                        (EnumerationExpandableIndex.frame callbackCore after)) output)
          | _ => True)) ∧'''
needle='''          | .stopped _ _ _ => True) ∧'''
assert header.count(needle)==1
header=header.replace(needle,append,1)
proof=''' := by
  obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
    headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
    shape, completedReceipt, callbackAdmission⟩ :=
    head_finite_complete_resources_with_callback_admission holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata recursiveFuel seed formulas solver recursive.forget inventory caller memos before uv handle scs
      parentEntry storedEdges depth free edge packet ready stored decoded selected incoming bounded known selectionMembers
      selectionLength capturedMass inherited initialMass inheritedLength reserved
  rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured⟩
  · exact ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
      headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
      .inl unsupported, completedReceipt, callbackAdmission⟩
  · cases receipt with
    | unhandled => cases advanced
    | rejected actual queries after =>
        exact ⟨headBound, .rejected actual queries after, middleCaller, saved, middleMemos, middleInventory,
          headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
          .inr ⟨outcome, advanced, callbackRun, resources, captured, trivial⟩, completedReceipt, callbackAdmission⟩
    | stopped fragments observation candidate =>
        exact ⟨headBound, .stopped fragments observation candidate, middleCaller, saved, middleMemos, middleInventory,
          headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
          .inr ⟨outcome, advanced, callbackRun, resources, captured, trivial⟩, completedReceipt, callbackAdmission⟩
    | complete fragment actual queries after =>
        have actualReceipt := completedReceipt fragment actual queries after rfl
        have admission := callbackAdmission fragment actual queries after rfl
        obtain ⟨callbackFuel, result, callbackCore, callbackOutcome,
          _returned, _stable, _frame, _types, _holes, _typing, callback, richRun,
          _richResources, returnedAdmission, histories⟩ :=
          SourcePruningEnumerationRecursive.callback_finite_complete_resources_with_history
            holeKey fits admits formulas solver middleInventory graph templates metadata uv fragment actual middleMemos after
            checkEmpty edgesOf stop order recursiveFuel recursive (afterHead seed inherited)
            (massCeil seed capturedMass inherited) admission.packet admission.allocated admission.bounded admission.known
            selectionMembers selectionLength admission.mass admission.reserved
        have outcomeSame : outcome = callbackOutcome := by
          have first := callbackRun callbackFuel
          have second := richRun headBound
          rw [Nat.add_comm callbackFuel headBound, actualReceipt.query] at second
          exact first.symm.trans second
        subst callbackOutcome
        refine ⟨headBound + callbackFuel, .complete fragment actual queries after,
          middleCaller, saved, middleMemos, middleInventory,
          ?_, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
          .inr ⟨outcome, advanced, ?_, resources, captured, ?_⟩, ?_, callbackAdmission⟩
        · intro extra
          simpa only [Nat.add_assoc] using headRun (callbackFuel + extra)
        · intro extra
          simpa only [Nat.add_assoc] using callbackRun (callbackFuel + extra)
        · refine ⟨result, callbackCore, ?_, returnedAdmission, ?_⟩
          · intro extra
            have actualCallback := callback (headBound + extra)
            have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
            rw [common] at actualCallback
            exact actualCallback
          · intro extra accepted output member
            have actualHistory := histories (headBound + extra) accepted output member
            have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
            rw [common] at actualHistory
            exact actualHistory
        · intro nextFragment nextCaller nextQueries nextCache completed
          have certificate := completedReceipt nextFragment nextCaller nextQueries nextCache completed
          exact { certificate with running := fun extra => by
            simpa only [Nat.add_assoc] using certificate.running (callbackFuel + extra) }

end MicroCFTA.SourcePruningEnumerationNativeHookResources
'''
text='''import MicroCFTA.SourcePruningEnumerationFiniteCallbackHistory
import MicroCFTA.SourcePruningEnumerationCallbackAdmission

/-!
# Actual native heads with admitted smaller-depth output histories

The original head producer supplies its same stable receipt and full memos.
A completed head admits the concrete callback at that exact returned cache.
One common bound covers the head, callback and every returned history.
-/
'''+ctx+'''/-- Retain the whole head packet and append actual false-callback output histories. -/\n'''+header+proof
(out/'SourcePruningEnumerationFiniteHeadHistory.lean').write_text(text)
(out/'revisions/001-initial.lean').write_text(text)
(out/'supported-history-appendix.txt').write_text(append)
