from pathlib import Path
import shutil,json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-prepared-history-20261028')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationCapturedEdgeSoundness.lean').read_text()
new=old.replace('''# Native soundness after actual captured-slot finalization

The actual expansion transports the neutral captured payload.
The final fragment equation restores the original pending restriction.''','''# Backward meaning through an actual prepared parent

The original stored value remains separate from the prepared parent.
Actual preparation supplies their independent language equivalence.
The actual completed receipt restores the original pending restriction.''')
new=new.replace('theorem stable_complete_sound_current','theorem stable_complete_sound_prepared',1)
new=new.replace('''    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))''','''    (sourceValue : Node)
    (decoded : lookupNode caller.checked.native.machine.heap handle = some sourceValue)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = [])
    (preparedMeaning : ∀ ambient term,
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient sourceValue term)''',1)
new=new.replace('''        assignment after.core →
      Satisfies''','''        assignment after.core →
      (Satisfies''',1)
new=new.replace('''      Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value''','''      Fragments.fill assignment fragment = assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient sourceValue (assignment uv) := by
  have available := parentAvailable
  have closed := parentClosed''',1)
new=new.replace('''exact (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mpr parentAccepted''','''exact (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mpr
          ((preparedMeaning ambient (Fragments.fill assignment fragment)).mp parentAccepted)''',1)
new=new.replace('''    exact ⟨original, by simpa only [equation] using edgeAccepted,
      by simpa only [equation] using parentAccepted,
      by simpa only [equation] using suspended, equation⟩''','''    refine ⟨⟨original, by simpa only [equation] using edgeAccepted,
      by simpa only [equation] using parentAccepted,
      by simpa only [equation] using suspended, equation⟩, ?_⟩
    exact (preparedMeaning ambient (assignment uv)).mp (by simpa only [equation] using parentAccepted)''',1)
p=area/'prepared-soundness/drafts/v1/SourcePruningEnumerationPreparedCapturedSoundness.lean';p.parent.mkdir(parents=True);p.write_text(new)
shutil.copyfile(p,root/'lean/MicroCFTA'/p.name)
mods=json.loads((area/'modules.json').read_text());mods.append(p.stem);(area/'modules.json').write_text(json.dumps(mods,indent=2)+'\n')
print(json.dumps(dict(bytes=len(new.encode()),module=p.stem)))
