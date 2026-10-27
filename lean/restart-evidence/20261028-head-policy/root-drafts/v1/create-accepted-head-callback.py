from pathlib import Path
import re,json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-head-policy-20261028')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationAcceptedHeadPolicy.lean').read_text()
pre=old[old.index('namespace MicroCFTA.'):old.index('/-- Each accepted')]
stmt=old[old.index('theorem head_finite_complete_resources_policy'):old.index(' := by')]
params,oldbody=stmt.split(' :\n    ∃ (bound : Nat)',1);names,body=oldbody.split(',\n      ',1)
params=params.replace('head_finite_complete_resources_policy','head_finite_complete_resources_callback_policy')
cb=(root/'lean/MicroCFTA/SourcePruningEnumerationCallbackRefutation.lean').read_text();cb=cb[cb.index('    ∃ fuel result after,\n')+len('    ∃ fuel result after,\n'):cb.index(' := by')]
replace={'fuel':'callbackFuel','after':'callbackAfter','before':'afterCache','caller':'actual','memos':'middleMemos','inventory':'middleInventory','profile':'(afterHead seed inherited).2','property':'(fun guard => guard ∈ (afterHead seed inherited).1)','width':'(bits + 2)','Result':'HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)'}
cb=re.sub(r'\b('+ '|'.join(re.escape(x) for x in replace)+r')\b',lambda m:replace[m.group()],cb)
observe='''
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core →
            InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient edge (assignment uv) →
            (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
              (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
            SourcePruningTemplates.Avoids templates (assignment uv) →
            (∀ program, SourcePruningTemplates.ProgramAt (assignment uv) program →
              SourcePruningTemplates.ProgramEncoding program) →
            ∃ extended : Nat → Language.Term Symbol,
              (∀ old < before.core.counter, extended old = assignment old) ∧
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient caller.checked.native.machine.heap)
                (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                extended before.core ∧
              Fragments.fill extended fragment = assignment uv ∧
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient actual.checked.native.machine.heap)
                (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                extended afterCache.core ∧
              result.1 = false ∧
              (∀ group ∈ result.2.pending, @SourcePruningResume.Refutes Symbol
                (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) extended group) ∧
              ∀ extra,
                continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                  (bound + callbackFuel + extra) recursiveFuel)
                  graph templates stop order (bound + callbackFuel + extra) metadata uv fragment actual queries afterCache =
                resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                  (bound + callbackFuel + extra) recursiveFuel result.2 actual queries
                  (EnumerationExpandableIndex.frame callbackAfter afterCache)
                  (SourcePruningEnumerationRestart.decision stop order result.2
                    (EnumerationExpandableIndex.frame callbackAfter afterCache))
'''
proof=''' := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, oldHead, policy⟩ :=
    head_finite_complete_resources_policy holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before uv handle scs parentEntry
      storedEdges depth free edge packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, ⟨oldHead, policy⟩, ?_⟩
  cases receipt with
  | unhandled | rejected _ _ _ | stopped _ _ _ => trivial
  | complete fragment actual queries afterCache =>
      obtain ⟨_running, post, _querySame, admitted, headPending, history, _cacheBounds, headFits,
        headKnown, shape, _accepting⟩ := oldHead
      have endpoint : actual = middleCaller ∧ queries = middleMemos.query := by
        rcases shape with unsupported | ⟨_outcome, advanced, _callback, _resources, _end⟩
        · cases unsupported.1
        · exact Prod.mk.inj (Option.some.inj advanced)
      subst actual
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have callbackPacket := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment afterCache
        level frontier post.context admitted history headPending ordered packet.bounded
      obtain ⟨callbackFuel, result, callbackAfter, callbackRetained, callbackSemantics⟩ :=
        SourcePruningEnumerationRecursive.callback_prefix_complete_resources_refutes formulas solver middleInventory
          graph templates metadata uv fragment middleCaller middleMemos afterCache
          holeKey fits admits checkEmpty edgesOf stop order callbackPacket admitted.2.2.1
          (afterHead seed inherited).2 (fun guard => guard ∈ (afterHead seed inherited).1) headFits headKnown
      refine ⟨callbackFuel, result, callbackAfter, ⟨callbackRetained, callbackSemantics⟩, ?_⟩
      intro ambient assignment satisfied accepted refuted avoids encoded
      obtain ⟨extended, produced, producedCache, agree, beforeModel, completed, filled, afterModel,
        self, pendingRefutes, currentAvoids, currentEncoding⟩ :=
        policy ambient assignment satisfied accepted refuted avoids encoded
      cases completed
      have semantic := callbackSemantics
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient middleCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        extended afterModel self pendingRefutes currentAvoids currentEncoding
      refine ⟨extended, agree, beforeModel, filled, afterModel, semantic.1, semantic.2, ?_⟩
      intro extra
      have actualCallback := (callbackRetained.1.2.2.2.2.2.2 (bound + extra)).2.2.1
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + callbackFuel + extra) recursiveFuel)
      have common : callbackFuel + (bound + extra) = bound + callbackFuel + extra := by omega
      rw [common, semantic.1] at actualCallback
      simpa only [endpoint.2, Bool.false_eq_true, ↓reduceIte] using actualCallback

end MicroCFTA.SourcePruningEnumerationNativeHookResources
'''
source='''import MicroCFTA.SourcePruningEnumerationAcceptedHeadPolicy
import MicroCFTA.SourcePruningEnumerationCallbackRefutation

/-!
# Actual callback continuation after an accepted native head

The head and callback bounds precede all original assignment observers.
The same captured cache supplies the actual callback resource certificate.
Original policy conditions derive non-rejection and the recursive continuation.
-/
'''+pre+'\n/-- An accepted original head derives non-rejection at its actual resource-bounded callback. -/\n'+params+' :\n    ∃ (bound : Nat)'+names+',\n      ('+body+') ∧\n      match (generalizing := false) receipt with\n      | .complete fragment actual queries afterCache =>\n          ∃ (callbackFuel : Nat) (result : Bool × SourcePruningRecordTypes.Metadata Typing)\n            (callbackAfter : EnumerationState.State Symbol Constraint),\n            ('+cb.strip()+') ∧\n'+observe+'      | _ => True'+proof
name='SourcePruningEnumerationAcceptedHeadCallback';p=area/'root-drafts/v1'/(name+'.lean');assert not p.exists();p.write_text(source);(root/'lean/MicroCFTA'/(name+'.lean')).write_text(source)
(area/'literal-head-policy-declaration.txt').write_text(stmt);(area/'literal-callback-refutation-return.txt').write_text(cb)
p=area/'modules.json';mods=json.loads(p.read_text());mods.append(name);p.write_text(json.dumps(mods,indent=2)+'\n');print(len(source),len(source.splitlines()))
