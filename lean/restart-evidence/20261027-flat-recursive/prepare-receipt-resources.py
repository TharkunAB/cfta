from pathlib import Path
r=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
old=(r/'SourcePruningEnumerationFiniteReceiptResources.lean').read_text()
s=old.replace('import MicroCFTA.SourcePruningEnumerationFiniteCallbackResources','import MicroCFTA.SourceFlatPruningRecursiveCallbackResources')
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationNativeHookResources','namespace MicroCFTA.SourceFlatPruningNativeHookResources')
s=s.replace('end MicroCFTA.SourcePruningEnumerationNativeHookResources','end MicroCFTA.SourceFlatPruningNativeHookResources')
s=s.replace('(Packet Output Failure continueWith resume Complete OutcomeResources)','(Packet Output Failure continueWith resume OutcomeResources)\nopen SourceFlatPruningRecursive (Complete)')
s=s.replace('local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result','local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result\nlocal notation "FlatReceipt" => SourceFlatPruningSelectedEdge.Result')
mark='''        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome := by'''
fam='''        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra (flatReceipt : FlatReceipt (bits + 2)),
        SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt →
        match (generalizing := false) flatReceipt with
        | .complete fragment actual saved after =>
            ∃ flatOutcome,
              SourceFlatPruningRecursive.continueWith
                (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                  (fuel + extra) recursiveFuel)
                graph templates stop order (fuel + extra) metadata uv fragment actual saved after = flatOutcome ∧
              SourceFlatPruningRecursive.ResultRelated flatOutcome outcome
        | _ => SourceFlatPruningRecursive.ResultRelated (.complete [] reached final.query) outcome) := by'''
assert s.count(mark)==1;s=s.replace(mark,fam)
s=s.replace('      exact ⟨0, .complete [] reached final.query, fun _ => rfl, originalResources.mono growth.1 growth.2⟩','''      refine ⟨0, .complete [] reached final.query, fun _ => rfl,
        originalResources.mono growth.1 growth.2, ?_⟩
      intro extra flatReceipt compared
      cases flatReceipt with
      | complete _ _ _ _ => cases compared
      | unhandled | rejected _ _ _ | stopped _ _ _ => exact ⟨.nil, rfl, rfl⟩''')
s=s.replace('_callback, running, resources⟩ :=','_callback, running, resources, flatRunning⟩ :=')
s=s.replace('SourcePruningEnumerationRecursive.callback_finite_complete_resources','SourceFlatPruningRecursive.callback_finite_complete_resources')
s=s.replace('      exact ⟨fuel, outcome, running, resources⟩','''      refine ⟨fuel, outcome, running, resources, ?_⟩
      intro extra flatReceipt compared
      cases flatReceipt with
      | unhandled | rejected _ _ _ | stopped _ _ _ => cases compared
      | complete flatFragment flatCaller flatQueries flatAfter =>
          obtain ⟨rfl, rfl, rfl, caches⟩ := compared
          exact flatRunning flatAfter caches extra''')
p=r/'SourceFlatPruningRecursiveReceiptResources.lean';assert not p.exists();p.write_text(s)
print('Prepared actual receipt callback resource composition.')
