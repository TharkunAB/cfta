from pathlib import Path
base=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeCoverage.lean')
s=base.read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationTraversalCoverage','import MicroCFTA.SourcePruningEnumerationTraversalCoverageOrigins\nimport MicroCFTA.SourcePruningEnumerationOrigins',1)
s=s.replace('# Constructive coverage of the actual selected edge','# Original term paths through the actual selected edge')
s=s.replace('Fresh witnesses preserve every variable in the original state.','Fresh witnesses preserve every variable in the original state.\nEquality witnesses and child holes retain paths in the original term.')
s=s.replace('open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies','open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies\nopen SourcePruningEnumerationOrigins',1)
s=s.replace('theorem complete_with_fragments_resources_accepting\n','theorem complete_with_fragments_resources_origins\n',1)
start=s.index('      (∀ er en P H ek,')
end=s.index(' := by\n  obtain',start)
old=s[start:end]
semantic=old[old.index('      ∀ (ambient :'):]
new=semantic.replace('(terms : List (Language.Term Symbol)),','(terms : List (Language.Term Symbol)) (whole : Language.Term Symbol),',1)
needle='(∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →\n        ∃'
assert needle in new
new=new.replace(needle,'(∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →\n        AssignmentOrigins whole before.core.counter assignment →\n        Origin whole (.node edge.entry.key.symbol terms) →\n        ∃',1)
new+=' ∧\n          AssignmentOrigins whole after.core.counter extended'
s=s[:start]+'      ('+old.lstrip()+') ∧\n'+new+s[end:]
s=s.replace('childResult, childrenRun, post, querySame, growth,','childResult, ⟨childrenRun, post, querySame, growth,',1)
s=s.replace('returnedFits, returnedKnown, childrenAccepting⟩ :=','returnedFits, returnedKnown, childrenAccepting⟩, childrenOrigins⟩ :=',1)
s=s.replace('SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_accepting seed','SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_accepting_origins seed',1)
modelstart=s.index('  have model :')
modelend=s.index('  have ownOrigin :',modelstart)
model=s[modelstart:modelend]
modelnew=model.replace('  have model :','  have modelOrigins :',1)
modelnew=modelnew.replace('(terms : List (Language.Term Symbol)),','(terms : List (Language.Term Symbol)) (whole : Language.Term Symbol),',1)
needle='(∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →\n      ∃'
assert needle in modelnew
modelnew=modelnew.replace(needle,'(∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →\n      AssignmentOrigins whole before.core.counter assignment →\n      Origin whole (.node edge.entry.key.symbol terms) →\n      ∃',1)
modelnew=modelnew.replace('residual (.node edge.entry.key.symbol terms) := by','residual (.node edge.entry.key.symbol terms) ∧\n        AssignmentOrigins whole after.core.counter extended := by',1)
modelnew=modelnew.replace('intro ambient assignment terms satisfied accepted guardHolds inherited','intro ambient assignment terms whole satisfied accepted guardHolds inherited origins termOrigin',1)
modelnew=modelnew.replace('⟨witnesses, ownSatisfied, freshAgree, freshHolds⟩ :=','⟨witnesses, ownSatisfied, freshAgree, freshHolds, ownOrigins⟩ :=',1)
modelnew=modelnew.replace('      fresh_classes_state_complete\n','      fresh_classes_state_complete_origins\n',1)
modelnew=modelnew.replace('before.core safe.1 assignment satisfied (.node edge.entry.key.symbol terms) tries equalities','before.core safe.1 assignment satisfied whole (.node edge.entry.key.symbol terms) tries equalities origins termOrigin',1)
modelnew=modelnew.replace('rw [← ownCore] at ownSatisfied','rw [← ownCore] at ownSatisfied ownOrigins',1)
modelnew=modelnew.replace('filled, afterSatisfied⟩ :=','filled, afterSatisfied, afterOrigins⟩ :=',1)
modelnew=modelnew.replace('childrenAccepting ambient','childrenOrigins ambient',1)
modelnew=modelnew.replace('witnesses terms ownSatisfied inputModels','witnesses terms whole ownSatisfied inputModels ownOrigins\n        (fun child member => origin_child whole edge.entry.key.symbol terms child termOrigin member)',1)
modelnew=modelnew.replace('afterSatisfied, residualHolds⟩','afterSatisfied, residualHolds, afterOrigins⟩',1)
s=s[:modelend]+modelnew+s[modelend:]
s=s.replace('.complete fragment afterCaller savedQueries finished, ?_, post, querySame, ?_, afterPaths,','.complete fragment afterCaller savedQueries finished, ⟨?_, post, querySame, ?_, afterPaths,',1)
s=s.replace('      returnedFits, returnedKnown, ?_⟩','      returnedFits, returnedKnown, ?_⟩, ?_⟩',1)
# Preserve the original complete-case observer and append its same-witness origin variant.
branch=s.index('    · intro ambient assignment terms satisfied accepted guardHolds inherited\n      obtain ⟨extended, agree')
branchend=s.index('  · subst childResult',branch)
proof=s[branch:branchend]
newproof=proof.replace('intro ambient assignment terms satisfied accepted guardHolds inherited','intro ambient assignment terms whole satisfied accepted guardHolds inherited origins termOrigin',1)
newproof=newproof.replace('afterSatisfied, residualHolds⟩ :=','afterSatisfied, residualHolds, afterOrigins⟩ :=',1)
newproof=newproof.replace('model ambient assignment terms satisfied accepted guardHolds inherited','modelOrigins ambient assignment terms whole satisfied accepted guardHolds inherited origins termOrigin',1)
newproof=newproof.replace('refine ⟨extended, fragment, agree, originalSatisfied, rfl, termSame, ?_⟩','refine ⟨extended, fragment, agree, originalSatisfied, rfl, termSame, ?_, afterOrigins⟩',1)
s=s[:branchend]+newproof+s[branchend:]
s=s.replace('      ?_, post, querySame, ?_, afterPaths, storage, afterRealized, afterCounts, afterFlags,','      ⟨?_, post, querySame, ?_, afterPaths, storage, afterRealized, afterCounts, afterFlags,',1)
s=s.replace('.inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown, ?_⟩','.inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown, ?_⟩, ?_⟩',1)
needle='      cases impossible\n\nend MicroCFTA.'
assert needle in s
s=s.replace(needle,'      cases impossible\n    · intro ambient assignment terms whole satisfied accepted guardHolds inherited origins termOrigin\n      obtain ⟨extended, _agree, _originalSatisfied, impossible, _filled, _afterSatisfied, _residualHolds, _origins⟩ :=\n        modelOrigins ambient assignment terms whole satisfied accepted guardHolds inherited origins termOrigin\n      cases impossible\n\nend MicroCFTA.',1)
out=Path('/tmp/mcfta-prepared-origins-20261028/ordinary-origins/drafts/v1/SourcePruningEnumerationSelectedEdgeOrigins.lean')
out.write_text(s)
