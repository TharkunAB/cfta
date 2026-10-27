from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-head-policy-20261028/accepted-head-review')
src=(repo/'lean/MicroCFTA/SourcePruningEnumerationFiniteHeadCoverage.lean').read_text()
start=src.index('/-- Keep the full finite head packet')
context=src[:start]
context=context.replace('import MicroCFTA.SourcePruningEnumerationFiniteHeadResources\nimport MicroCFTA.SourcePruningEnumerationNativeHeadCoverage', 'import MicroCFTA.SourcePruningEnumerationFiniteHeadCoverage\nimport MicroCFTA.SourcePruningAssignmentRefutation')
a=src.index('theorem head_finite_complete_resources_accepting',start);z=src.index(' := by',a);decl=src[a:z]
newname='head_finite_complete_resources_policy'
newdecl=decl.replace('head_finite_complete_resources_accepting',newname,1)
marker='      (∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty'
assert newdecl.count(marker)==1
newdecl=newdecl.replace(marker,'      ((∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty',1)
canonical='(@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)'
observer=''' ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
          CANONICAL assignment group) →
        SourcePruningTemplates.Avoids templates (assignment uv) →
        (∀ program, SourcePruningTemplates.ProgramAt (assignment uv) program →
          SourcePruningTemplates.ProgramEncoding program) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (afterCache : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          receipt = .complete fragment middleCaller saved afterCache ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient middleCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended afterCache.core ∧
          Fragments.fill extended fragment = extended uv ∧
          (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
            CANONICAL extended group) ∧
          SourcePruningTemplates.Avoids templates (Fragments.fill extended fragment) ∧
          ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill extended fragment) program →
            SourcePruningTemplates.ProgramEncoding program'''.replace('CANONICAL',canonical)
proof=''' := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, retained⟩ :=
    head_finite_complete_resources_accepting holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before uv handle scs parentEntry
      storedEdges depth free edge packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, retained, ?_⟩
  obtain ⟨_running, _post, _queries, _admitted, _pending, _history, _cacheBounds, _headFits,
    _headKnown, _shape, accepting⟩ := retained
  intro ambient assignment satisfied accepted refuted avoids encoded
  obtain ⟨extended, fragment, afterCache, agree, beforeModel, completed, filled, afterModel⟩ :=
    accepting ambient assignment satisfied accepted
  have self : Fragments.fill extended fragment = extended uv :=
    filled.trans (agree uv ready.inside).symm
  have pendingRefutes : ∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
      CANONICAL extended group := by
    intro group member
    exact (@SourcePruningResume.refutes_assignment_congr Symbol
      CANONICAL
      before.core.counter assignment extended group (packet.bounded group member) agree).mpr (refuted group member)
  refine ⟨extended, fragment, afterCache, agree, beforeModel, completed, filled, afterModel,
    self, pendingRefutes, ?_, ?_⟩
  · rw [filled]
    exact avoids
  · rw [filled]
    exact encoded

end MicroCFTA.SourcePruningEnumerationNativeHookResources
'''.replace('CANONICAL',canonical)
text=context+'/-- Each accepted original head derives the semantic conditions for its actual callback input. -/\n'+newdecl+')'+observer+proof
p=out/'drafts/v1/SourcePruningEnumerationAcceptedHeadPolicy.lean';assert not p.exists();p.write_text(text)
# Retain literal original declaration and independent inverse of the added observer/group.
(out/'contracts').mkdir(exist_ok=True);(out/'contracts/old-head-accepting-declaration.txt').write_text(decl)
recovered=newdecl.replace('head_finite_complete_resources_policy','head_finite_complete_resources_accepting',1).replace('      ((∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty',marker,1)
assert recovered==decl;(out/'contracts/recovered-head-accepting-declaration.txt').write_text(recovered)
(out/'draft-contract-comparison.json').write_text(json.dumps({'entire_original_declaration_exact':True,'bytes':len(decl.encode()),'sha256':hashlib.sha256(decl.encode()).hexdigest(),'one_old_producer_call':text.count('    head_finite_complete_resources_accepting holeKey')==1,'new_semantics_after_all_fixed_witnesses':True,'new_producer_admission':False,'status':'UNTESTED'},indent=2)+'\n')
b=p.read_bytes();print(json.dumps({'path':str(p),'bytes':len(b),'lines':len(b.splitlines()),'sha256':hashlib.sha256(b).hexdigest(),'old_declaration_bytes':len(decl.encode())},indent=2))
