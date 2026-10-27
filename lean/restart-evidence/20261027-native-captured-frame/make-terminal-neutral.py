from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
s=(root/'lean/MicroCFTA/SourcePruningEnumerationTerminalLanguage.lean').read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationIncomingStableLanguage','import MicroCFTA.SourcePruningEnumerationIncomingStableNeutral\nimport MicroCFTA.SourcePruningEnumerationTerminalPrefixNeutral\nimport MicroCFTA.SourcePruningEnumerationFoldObservedNeutral')
s=s.replace('# Exact assignment language of the complete actual terminal arm','# Neutral assignment language of the complete actual terminal arm')
s=s.replace('theorem run_complete_semantics','theorem run_complete_neutral_semantics',1)
s=s.replace('      ∀ (ambient : InternedGuardedLanguage.Env Symbol)','      ∀ (held : Nat), Avoids before.representatives held (first :: rest) →\n      ∀ (ambient : InternedGuardedLanguage.Env Symbol)',1)
s=s.replace('residualMeaning assignment output) ↔','residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔')
s=s.replace('residualMeaning assignment before ∧','residualMeaning assignment (EnumerationFrame.neutralize held before) ∧')
s=s.replace('classes, _joinedPaths, prefixMeaning⟩','classes, _joinedPaths, _prefixMeaning⟩')
s=s.replace('    foldMeaning⟩ := SourcePruningEnumerationFold.run_complete_semantics','    _foldMeaning⟩ := SourcePruningEnumerationFold.run_complete_semantics')
pos=s.index('  have actualFoldMeaning')
s=s[:pos]+'''  intro held avoids
  have sourcesOther : ∀ source ∈ recorded, source ≠ held := by
    intro source member same
    rw [recordedSame] at member
    obtain ⟨sc, present, rootSame⟩ := List.mem_map.mp member
    apply avoids sc present
    obtain ⟨size, path⟩ := paths sc.var
    have equal : roots sc.var = held := rootSame.trans same
    exact UnionFind.sameClass_symm (by simpa only [equal] using UnionFind.sameClass_root path)
  have winnerOther : winner ≠ held := sourcesOther winner winnerMember
  have prefixMeaning := SourcePruningEnumerationTerminalPrefix.neutral_semantics held r first rest waiting
    before joined recorded winner moved safe.1.total
    (by rw [Success, prefixObserved]; exact List.mem_singleton_self _)
''' +s[pos:]
s=s.replace('residualMeaning assignment joined := by','residualMeaning assignment (EnumerationFrame.neutralize held joined) := by')
s=s.replace('    simpa only [← rawSame, ← callersSame] using foldMeaning ambient residualMeaning assignment classes','''    exact SourcePruningEnumerationFold.observed_neutral_semantics formulas solver inventory beforeCaller joined
      recorded checkEmpty winner memos initial joinedRealized winnerPending
      (fun source member => .inr (sourcesPending source member)) foldRanges held winnerOther sourcesOther
      foldObserved ambient residualMeaning assignment classes''')
s=s.replace('SourcePruningEnumerationIncomingNode.stable_semantics','SourcePruningEnumerationIncomingNode.stable_neutral_semantics')
s=s.replace('closed foldedBounded incomingRanges\n','closed foldedBounded incomingRanges held winnerOther\n')
(root/'lean/MicroCFTA/SourcePruningEnumerationTerminalNeutralLanguage.lean').write_text(s)
