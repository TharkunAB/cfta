from pathlib import Path
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');o=Path('/tmp/mcfta-prepared-composition-20261028/sibling-origins')
old=(root/'SourcePruningEnumerationPreparedFiniteReceiptModels.lean').read_text();s=old[:old.index(' := by\n  have recursive')]
s=s.replace('import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources\nimport MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptResources\nimport MicroCFTA.SourcePruningEnumerationPreparedCallbackModels','import MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptModels\nimport MicroCFTA.SourcePruningEnumerationPolicyOrigins',1)
a=s.index('/-!');z=s.index('-/',a)+2
s=s[:a]+'''/-!
# Original subtree policies at the actual prepared receipt restart

The old receipt model producer fixes every operational witness once.
The complete branch retains that same recorded metadata and callback core.
Its actual recording frame preserves every allocated original path.
Original subtree policies supply the old callback model conditions.
No model of recursive outputs is an input or a conclusion.
-/'''+s[z:]
s=s.replace('open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame','open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame\nopen SourcePruningEnumerationOrigins',1)
s=s.replace('theorem receipt_finite_complete_resources_models\n','theorem receipt_finite_complete_resources_origins\n',1)
a=s.index('            Packet formulas solver next actual final metadata afterCache ∧')
z=s.index('\n      | _ => True',a);retained=s[a:z]
start=retained.index('            ∀ (language : NodeLanguage Symbol)\n')
observer=retained[start:]
observer=observer.replace('(assignment : Nat → Language.Term Symbol),','(assignment : Nat → Language.Term Symbol)\n              (whole : Language.Term Symbol),',1)
needle='''              SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) →
              (∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
                SourcePruningTemplates.ProgramEncoding program) →'''
replacement='''              SourcePruningTemplates.OriginPolicies templates whole →
              Origin whole (assignment uv) →'''
assert needle in observer;observer=observer.replace(needle,replacement,1)
iff='''            (∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
              AssignmentOrigins whole callbackCore.counter assignment ↔
                AssignmentOrigins whole afterCache.core.counter assignment)'''
s=s[:a]+'            ('+retained.lstrip()+') ∧\n'+iff+' ∧\n'+observer+s[z:]
s+=''' := by
  obtain ⟨fuel, outcome, resources, completedModels⟩ :=
    receipt_finite_complete_resources_models holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata formulas solver recursiveFuel original next caller reached memos final before uv receipt
      packet post advanced admitted pending history seed ceiling bounded known selectionMembers selectionLength
      mass reserved
  cases receipt with
  | unhandled => exact ⟨fuel, outcome, resources, completedModels⟩
  | rejected actual saved after => exact ⟨fuel, outcome, resources, completedModels⟩
  | stopped fragments observation candidate => exact ⟨fuel, outcome, resources, completedModels⟩
  | complete fragment actual saved afterCache =>
      obtain ⟨actualSame, savedSame, recorded, callbackCore, current, allocated, returned, equivalence, models⟩ :=
        completedModels
      refine ⟨fuel, outcome, resources, actualSame, savedSame, recorded, callbackCore,
        ⟨current, allocated, returned, equivalence, models⟩, ?_, ?_⟩
      · intro whole assignment
        rw [returned.2.2.1.counter]
      · intro language meaning assignment whole satisfied filled refuted policies origin
        have localPolicies := policies (assignment uv) origin
        have avoids : SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) := by
          simpa only [filled] using localPolicies.1
        have encoded : ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
            SourcePruningTemplates.ProgramEncoding program := by
          simpa only [filled] using localPolicies.2
        exact models language meaning assignment satisfied filled refuted avoids encoded

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
'''
p=o/'drafts/v1/SourcePruningEnumerationPreparedFiniteReceiptOrigins.lean';p.write_text(s)
