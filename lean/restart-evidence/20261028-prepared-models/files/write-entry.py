from pathlib import Path
import re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
old=(root/'SourcePruningEnumerationPrefixAdmission.lean').read_text()
header=old[old.index('namespace MicroCFTA.SourcePruningEnumerationPrefixAdmission'):old.index('/-- Sum every original')]
header=header.replace('SourcePruningEnumerationPrefixAdmission','SourcePruningEnumerationPreparedEntryModels',1)
sig=old[old.index('theorem narrowed_admission'):old.index(' := by',old.index('theorem narrowed_admission'))]
sig=sig.replace('theorem narrowed_admission','theorem narrowed_preparation_complete_models')
sig=sig.replace('    (valid : PrefixValid', '''    (actual : runPrefix holeKey fits admits graph templates stop order metadata
      fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed)
    (valid : PrefixValid''')
sig=sig.replace('          Post formulas solver inventory caller reached final','          (Post formulas solver inventory caller reached final',1)
sig=sig.replace('suspendedBound before.core','SourcePruningEnumerationPrefixAdmission.suspendedBound before.core')
start=sig.index('    | _ => True')
sig=sig[:start].rstrip()+') ∧\n'
prep=(root/'SourcePruningEnumerationPreparedPreparationResources.lean').read_text();prep=prep[prep.index('    ∃ (bound : Nat)'):prep.index(' := by',prep.index('    ∃ (bound : Nat)'))]
prep=prep.replace('bound','preparationBound')
for before,after in [('caller','reached'),('before','after'),('memos','final')]:prep=re.sub(r'\b'+before+r'\b',after,prep)
prep=re.sub(r'\bprofile\b','(headProfile profile)',prep)
prep=prep.replace(' run (',' SourcePruningEnumerationSelectedPreparation.run (')
sig+='\n'.join('      '+line for line in prep.splitlines())+' ∧\n'
sig+='''            Post formulas solver inventory caller
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap) final ∧
'''
model=(root/'SourcePruningEnumerationPrefixModels.lean').read_text();obs=model[model.index('        ∀ (ambient'):model.index('          match SourcePruningEnumerationSelectedStep.runPrefix',model.index('        ∀ (ambient'))]
obs=obs.replace('selected','uv')
sig+=obs+'''          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient heap)
            residualMeaning assignment entered.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient result (assignment uv)
    | _ => True'''
body=''' := by
  have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel uv caller memos before packet chosen profile property bounded known observed valid
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have ready := (SourcePruningEnumerationRestart.selected stop order metadata caller before uv
    packet.valid packet.safe chosen).1
  have currentValid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query) := by
    simpa only [actual] using valid
  have models := SourcePruningEnumerationSelectedStep.prefix_accepting
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel uv caller before memos packet.context ready realized currentValid
  rw [actual] at models
  cases observed with
  | stopped _ _ | parked _ _ _ => trivial
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨handle, scs, value, final, retained⟩ := admission
          obtain ⟨post, saved, afterPacket, afterReady, stored, _decoded, _available, _closed,
            _incoming, _pending, _ids, _lengths, _counter, _waiting, afterFits, afterKnown⟩ := retained
          obtain ⟨preparationBound, decoded, result, heap, entered, preparation, preparedKnown⟩ :=
            SourcePruningEnumerationSelectedPreparation.complete_resources_known formulas solver inventory
              reached final metadata after uv handle scs afterPacket afterReady stored
              (headProfile profile) afterFits property afterKnown
          have originalPreparation := And.intro preparation preparedKnown
          obtain ⟨preparedPacket, _preparedFits, _preparedMass⟩ := preparation
          obtain ⟨_preparationRun, _lookup, preparationPost, _enteredPacket, _stable,
            _enteredReady, _enteredStored, _counterSame, _values, _flags, _waiting,
            _resultAvailable, _resultClosed, _language, preparedModels⟩ := preparedPacket
          refine ⟨handle, scs, value, final, retained, preparationBound, decoded, result,
            heap, entered, originalPreparation, post.trans preparationPost, ?_⟩
          intro ambient residualMeaning assignment satisfied unary application filtered
          have afterSatisfied := models ambient residualMeaning assignment satisfied unary application filtered
          have prepared := preparedModels (SourceEqualityPCSGuard.holds formulas solver)
            ambient residualMeaning assignment
          exact ⟨prepared.1.mpr afterSatisfied, prepared.2 afterSatisfied⟩

end MicroCFTA.SourcePruningEnumerationPreparedEntryModels
'''
imports='''import MicroCFTA.SourcePruningEnumerationPrefixCheckpointModels
import MicroCFTA.SourcePruningEnumerationPrefixAdmission
import MicroCFTA.SourcePruningEnumerationPreparedPreparationResources

/-!
# Original models through the actual prefix and one native preparation

The original packet supplies every retained prefix and preparation field.
The stored narrowed handle and the prepared result remain distinct.
The same original assignment satisfies the actual entered cache and accepts
its prepared value under the original annotation policies.
No recursive output model or future branch success is an input.
-/
'''
(root/'SourcePruningEnumerationPreparedEntryModels.lean').write_text(imports+header+'/-- Retain actual admission and preparation resources, then transport the original model. -/\n'+sig+body)
