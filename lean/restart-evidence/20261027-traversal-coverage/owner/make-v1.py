from pathlib import Path
import hashlib
src=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationTraversalResources.lean').read_text()
a=src.index('/-- Original resources retain the full traversal packet')
b=src.index('/-- Original resources retain the full earlier traversal interface')
body=src[a:b]
body=body.replace('/-- Original resources retain the full traversal packet and its actual returned caller. -/', '/-- Original accepted terms construct the same complete traversal and preserve all old resources. -/')
body=body.replace('theorem complete_with_fragments_resources\n','theorem complete_with_fragments_resources_accepting\n',1)
marker='''      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap := by'''
observer='''      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol) (terms : List (Language.Term Symbol)),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core →
        Language.All₂ (fun input term =>
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds assignment term sc) inputs terms →
        ∃ extended : Nat → Language.Term Symbol,
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core ∧
          result = .complete fragments afterCaller savedQueries after ∧
          fragments.map (Fragments.fill extended) = terms ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core := by'''
assert marker in body;body=body.replace(marker,observer,1)
body=body.replace('''.inl ⟨rfl, safe, by simp⟩, fits, known⟩''','''.inl ⟨rfl, safe, by simp⟩, fits, known, ?_⟩''',1)
needle='''      · simp
  | cons input rest ih =>'''
replace='''      · simp
      · intro ambient residualMeaning assignment terms satisfied related
        cases related
        exact ⟨assignment, fun _ _ => rfl, satisfied, rfl, rfl, satisfied⟩
  | cons input rest ih =>'''
assert needle in body;body=body.replace(needle,replace,1)
needle='''        middleRoots, outer, waiting, headRun, headPost, headQueries, growth, middlePaths,
        middleStorage, middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        headReferences, headPending, shape, middleFits, middleKnown⟩ :=
        SourcePruningEnumerationChildCompletion.complete_with_fragments_resources seed formulas solver inventory beforeCaller before'''
replace='''        middleRoots, outer, waiting, ⟨headRun, headPost, headQueries, growth, middlePaths,
        middleStorage, middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        headReferences, headPending, shape, middleFits, middleKnown, _headTerminal⟩, headAccepting⟩ :=
        SourcePruningEnumerationChildCompletion.complete_with_fragments_resources_accepting seed formulas solver inventory beforeCaller before'''
assert needle in body;body=body.replace(needle,replace,1)
body=body.replace('''headPending, ?_, .inr ⟨outer, waiting, rfl⟩, ?_, ?_⟩''','''headPending, ?_, .inr ⟨outer, waiting, rfl⟩, ?_, ?_, ?_⟩''',1)
needle='''            (advance seed (bucket.length + 1)) (cost rest) (middleKnown key edge found)
      · have tailGenuine'''
replace='''            (advance seed (bucket.length + 1)) (cost rest) (middleKnown key edge found)
        · intro ambient residualMeaning assignment terms satisfied related
          cases related with
          | cons head _tail =>
              obtain ⟨_extended, _fragment, _agree, _original, singleton, _filled, _satisfied⟩ :=
                headAccepting ambient residualMeaning assignment _ satisfied head.1 head.2
              cases singleton
      · have tailGenuine'''
assert needle in body;body=body.replace(needle,replace,1)
body=body.replace('''tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown⟩ :=''', '''tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown, tailAccepting⟩ :=''')
body=body.replace('''(fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown⟩''','''(fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown, ?_⟩''',1)
append='''        · intro ambient residualMeaning assignment terms satisfied related
          cases related with
          | @cons input term rest terms headModel tailModels =>
              obtain ⟨headAssignment, headFragment, headAgree, _originalHead, headSingleton,
                headFill, middleSatisfied⟩ :=
                headAccepting ambient residualMeaning assignment term satisfied headModel.1 headModel.2
              have headMember : Except.ok (headFragment, middle.core) ∈
                  ([.ok (fragment, middle.core)] : List (Except EnumerationState.Error
                    (Fragment × EnumerationState.State Symbol Constraint))) := by
                rw [← singleton, headSingleton]
                exact List.mem_singleton_self _
              have headFragmentSame : headFragment = fragment :=
                congrArg Prod.fst (Except.ok.inj (List.mem_singleton.mp headMember))
              have firstTerm : Fragments.fill headAssignment fragment = term := by
                simpa only [headFragmentSame] using headFill
              have transfer : ∀ (entries : List (Node × List Suspended))
                  (values : List (Language.Term Symbol)),
                  (∀ value bucket, (value, bucket) ∈ entries →
                    ∀ sc ∈ bucket, sc.var < before.core.counter) →
                  Language.All₂ (fun input term =>
                    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                      ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds assignment term sc) entries values →
                  Language.All₂ (fun input term =>
                    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                      ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds headAssignment term sc) entries values := by
                intro entries
                induction entries with
                | nil =>
                    intro values _bounds models
                    cases models
                    exact .nil
                | cons entry entries ih =>
                    intro values bounds models
                    cases models with
                    | cons first remaining =>
                        refine .cons ⟨first.1, ?_⟩ (ih _ ?_ remaining)
                        · intro sc member
                          exact EnumerationConstruction.holds_extension assignment headAssignment
                            before.core.counter headAgree sc (bounds entry.1 entry.2 (by simp) sc member)
                            _ (first.2 sc member)
                        · intro value bucket member
                          exact bounds value bucket (List.mem_cons_of_mem _ member)
              have tailModelsExtended := transfer rest terms (by
                intro value bucket member
                exact (genuine value bucket (List.mem_cons_of_mem _ member)).2.2.1) tailModels
              obtain ⟨extended, tailAgree, _middleExtended, tailComplete, tailFilled, afterSatisfied⟩ :=
                tailAccepting ambient residualMeaning headAssignment terms middleSatisfied tailModelsExtended
              have agree : ∀ uv < before.core.counter, extended uv = assignment uv := by
                intro uv inside
                exact (tailAgree uv (Nat.lt_of_lt_of_le inside growth)).trans (headAgree uv inside)
              have originalExtended : Satisfies
                  (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                    ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core :=
                (EnumerationCorrectness.state_assignment_congr _ _ before.core safe.1 extended assignment agree).mpr
                  satisfied
              refine ⟨extended, agree, originalExtended, ?_, ?_, afterSatisfied⟩
              · dsimp only [result]
                rw [tailComplete]
              · simp only [List.map_cons, tailFilled]
                rw [EnumerationCorrectness.fill_bounded middle.core.counter extended headAssignment
                  tailAgree fragment fragmentBound, firstTerm]
'''
body=body.rstrip()+'\n'+append
preamble='''import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationChildCoverage

/-!
# Constructive coverage of resource-admitted child traversal

The actual head supplies the caller, full memos and cache for its suffix.
Every accepted ordered input constructs a successful child singleton.
Fresh assignment changes preserve every earlier fragment filling.
The full original traversal packet and resource schedule remain available.
-/
'''
a=src.index('namespace MicroCFTA.');b=src.index('/-- Each original child bucket')
preamble+=src[a:b]
preamble=preamble.replace('open EnumerationState','open Language EnumerationState',1)
result=preamble+body+'\nend MicroCFTA.SourcePruningEnumerationTraversalCompletion\n'
p=Path('/tmp/mcfta-traversal-coverage-20261027/owner/drafts/v1/SourcePruningEnumerationTraversalCoverage.lean');p.write_text(result)
print('path',p,'lines',len(result.splitlines()),'bytes',len(result.encode()),'sha256',hashlib.sha256(result.encode()).hexdigest())
