from pathlib import Path
base=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean')
s=base.read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationChildCoverage','import MicroCFTA.SourcePruningEnumerationChildCoverageOrigins\nimport MicroCFTA.SourcePruningEnumerationOrigins')
s=s.replace('# Constructive coverage of resource-admitted child traversal','# Original term paths through resource-admitted child traversal')
s=s.replace('Fresh assignment changes preserve every earlier fragment filling.','Fresh assignment changes preserve every earlier fragment filling.\nThe same assignment retains an original term path at every allocated variable.')
s=s.replace('open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies','open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies\nopen SourcePruningEnumerationOrigins')
s=s.replace('theorem complete_with_fragments_resources_accepting\n','theorem complete_with_fragments_resources_accepting_origins\n',1)
start=s.index('      (∀ extraRepresentative')
end=s.index(' := by\n  induction inputs',start)
old=s[start:end]
semstart=old.index('      ∀ (ambient :')
semantic=old[semstart:]
new=semantic.replace('(terms : List (Language.Term Symbol)),','(terms : List (Language.Term Symbol)) (whole : Language.Term Symbol),',1)
needle=' inputs terms →\n        ∃ extended'
assert needle in new
new=new.replace(needle,' inputs terms →\n        AssignmentOrigins whole before.core.counter assignment →\n        (∀ term ∈ terms, Origin whole term) →\n        ∃ extended',1)
new += ' ∧\n          AssignmentOrigins whole after.core.counter extended'
s=s[:start]+'      ('+old.lstrip()+') ∧\n'+new+s[end:]
# Add the outer retained packet grouping at the three constructive branches.
s=s.replace('.complete [] beforeCaller memos.query before, ?_, Post.refl initial, rfl, Nat.le_refl _,','.complete [] beforeCaller memos.query before, ⟨?_, Post.refl initial, rfl, Nat.le_refl _,',1)
s=s.replace('(fun valid => valid), ?_, .inl ⟨rfl, safe, by simp⟩, fits, known, ?_⟩','(fun valid => valid), ?_, .inl ⟨rfl, safe, by simp⟩, fits, known, ?_⟩, ?_⟩',1)
needle='        exact ⟨assignment, fun _ _ => rfl, satisfied, rfl, rfl, satisfied⟩\n  | cons'
s=s.replace(needle,'        exact ⟨assignment, fun _ _ => rfl, satisfied, rfl, rfl, satisfied⟩\n      · intro ambient residualMeaning assignment terms whole satisfied related origins _termOrigins\n        cases related\n        exact ⟨assignment, fun _ _ => rfl, satisfied, rfl, rfl, satisfied, origins⟩\n  | cons',1)
s=s.replace('middleRoots, outer, waiting, ⟨headRun,','middleRoots, outer, waiting, ⟨⟨headRun,',1)
s=s.replace('_headTerminal⟩, headAccepting⟩ :=','_headTerminal⟩, headAccepting⟩, headOrigins⟩ :=',1)
s=s.replace('SourcePruningEnumerationChildCompletion.complete_with_fragments_resources_accepting seed','SourcePruningEnumerationChildCompletion.complete_with_fragments_resources_accepting_origins seed',1)
s=s.replace('          ?_, headPost, headQueries, growth, middlePaths,','          ⟨?_, headPost, headQueries, growth, middlePaths,',1)
s=s.replace('middleFlags, headOrigin, protects, ?_, ?_, headPending, ?_, .inr ⟨outer, waiting, rfl⟩, ?_, ?_, ?_⟩','middleFlags, headOrigin, protects, ?_, ?_, headPending, ?_, .inr ⟨outer, waiting, rfl⟩, ?_, ?_, ?_⟩, ?_⟩',1)
needle='              cases singleton\n      · have tailGenuine'
s=s.replace(needle,'              cases singleton\n        · intro ambient residualMeaning assignment terms whole satisfied related origins termOrigins\n          cases related with\n          | cons head _tail =>\n              obtain ⟨_extended, _fragment, _agree, _original, singleton, _filled, _satisfied, _origins⟩ :=\n                headOrigins ambient residualMeaning assignment _ whole satisfied head.1 head.2 origins\n                  (termOrigins _ (by simp))\n              cases singleton\n      · have tailGenuine',1)
s=s.replace('final, next, afterRoots, tailResult, tailRun, tailPost,','final, next, afterRoots, tailResult, ⟨tailRun, tailPost,',1)
s=s.replace('tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown, tailAccepting⟩ :=','tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown, tailAccepting⟩, tailOrigins⟩ :=',1)
s=s.replace('          ?_, headPost.trans tailPost, querySame, Nat.le_trans growth tailGrowth, afterPaths,','          ⟨?_, headPost.trans tailPost, querySame, Nat.le_trans growth tailGrowth, afterPaths,',1)
s=s.replace('(fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown, ?_⟩','(fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown, ?_⟩, ?_⟩',1)
# Reuse the exact model composition proof for the appended origin observer.
branch=s.index('        · intro ambient residualMeaning assignment terms satisfied related\n          cases related with\n          | @cons')
proof=s[branch:s.index('\n\nend MicroCFTA.',branch)]
proof=proof.replace('intro ambient residualMeaning assignment terms satisfied related','intro ambient residualMeaning assignment terms whole satisfied related origins termOrigins',1)
proof=proof.replace('headFill, middleSatisfied⟩ :=','headFill, middleSatisfied, middleOrigins⟩ :=',1)
proof=proof.replace('headAccepting ambient residualMeaning assignment term satisfied headModel.1 headModel.2','headOrigins ambient residualMeaning assignment term whole satisfied headModel.1 headModel.2\n                  origins (termOrigins term (by simp))',1)
proof=proof.replace('tailComplete, tailFilled, afterSatisfied⟩ :=','tailComplete, tailFilled, afterSatisfied, afterOrigins⟩ :=',1)
proof=proof.replace('tailAccepting ambient residualMeaning headAssignment terms middleSatisfied tailModelsExtended','tailOrigins ambient residualMeaning headAssignment terms whole middleSatisfied tailModelsExtended\n                  middleOrigins (fun child member => termOrigins child (List.mem_cons_of_mem _ member))',1)
proof=proof.replace('refine ⟨extended, agree, originalExtended, ?_, ?_, afterSatisfied⟩','refine ⟨extended, agree, originalExtended, ?_, ?_, afterSatisfied, afterOrigins⟩',1)
s=s.replace('\n\nend MicroCFTA.', '\n'+proof+'\n\nend MicroCFTA.',1)
out=Path('/tmp/mcfta-prepared-origins-20261028/ordinary-origins/drafts/v1/SourcePruningEnumerationTraversalCoverageOrigins.lean')
out.write_text(s)
