from pathlib import Path
r=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
old=(r/'SourcePruningEnumerationNativeBranchResources.lean').read_text()
cut=old.index('\n/-- Original resources retain all receipt histories')
s=old[:cut]
s=s.replace('import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion\nimport MicroCFTA.SourcePruningEnumerationCapturedEdgeResources','import MicroCFTA.SourcePruningEnumerationNativeBranchResources\nimport MicroCFTA.SourceFlatPruningCapturedResources\nimport MicroCFTA.SourceFlatPruningNativeBranches')
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion','namespace MicroCFTA.SourceFlatPruningNativeHeadResources')
s=s.replace('# Original resources through ordered native alternatives','# Actual flat heads from original resource admission')
start=s.index('/-- Count the original projected child cost');end=s.index('variable [DecidableEq Symbol]',start)
s=s[:start]+'open SourcePruningEnumerationNativeBranchCompletion (CacheValid Admitted Pending FragmentHistory edgeCost)\n\n'+s[end:]
s=s.replace('local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint','local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint\nlocal notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint')
mark='        afterCaller.checked.native.machine.heap := by'
assert s.count(mark)>=1
s=s.replace(mark,'''        afterCaller.checked.native.machine.heap ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ en P H, p ≤ P → h ≤ H →
          ∃ flatReceipt,
            SourceFlatPruningCapturedEdge.run checkEmpty (n + en) P H uv scs edge
              caller flat memos.query = some flatReceipt ∧
            SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt) := by''',1)
s=s.replace('          ?_, ?_⟩\n        · intro er','          ?_, ?_, ?_⟩\n        · intro er',1)
unsupported='''        · intro flat _related en P H _largeP _largeH
          refine ⟨.unhandled, ?_, trivial⟩
          simp only [SourceFlatPruningCapturedEdge.run, SourceFlatPruningSelectedEdge.run,
            SourceFlatPruningCachedOwn.prepare, allowed, ↓reduceIte, projected]
'''
mark='    | some pair =>';assert s.count(mark)==1;s=s.replace(mark,unsupported+mark)
s=s.replace('pendingHistory, shape, returnedFits, returnedKnown⟩ :=','pendingHistory, shape, returnedFits, returnedKnown, flatRunning⟩ :=')
s=s.replace('SourcePruningEnumerationCapturedEdge.complete_with_history_resources seed','SourceFlatPruningCapturedResources.complete_with_history_resources seed')
s=s.replace('.inl rfl, headFits, headKnown⟩','.inl rfl, headFits, headKnown, ?_⟩')
flathead='''          intro flat related en P H largeP largeH
          obtain ⟨flatReceipt, actual, compared, _correct⟩ := flatRunning flat related en P H largeP largeH
          exact ⟨flatReceipt, actual, compared⟩
'''
s=s.replace('          exact ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,','          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,')
mark='        · subst result\n';assert s.count(mark)==2
first=s.index(mark);second=s.index(mark,first+1);s=s[:second]+flathead+s[second:]
mark='  · have rejected';assert s.count(mark)==1;s=s.replace(mark,flathead+mark)
s=s.replace('      ?_, ?_⟩\n    · intro er','      ?_, ?_, ?_⟩\n    · intro er')
s+='''    · intro flat related en P H _largeP _largeH
      refine ⟨.rejected caller memos.query flat, ?_, rfl, rfl, related⟩
      simp only [SourceFlatPruningCapturedEdge.run, SourceFlatPruningSelectedEdge.run,
        SourceFlatPruningCachedOwn.prepare, rejected, Bool.false_eq_true, ↓reduceIte]

end MicroCFTA.SourceFlatPruningNativeHeadResources
'''
p=r/'SourceFlatPruningNativeHeadResources.lean';assert not p.exists();p.write_text(s)
print('Prepared actual native head resource transport.')
