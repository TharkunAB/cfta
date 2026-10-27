from pathlib import Path
import hashlib,json,datetime
root=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-selector-capture-20261027/captured-owner')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationCapturedEdgeResources.lean').read_text()
header=old[:old.index('/-- Initial resources retain the full captured-slot history')]
header=header.replace('import MicroCFTA.SourcePruningEnumerationCapturedEdge\nimport MicroCFTA.SourcePruningEnumerationSelectedEdgeResources','''import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources
import MicroCFTA.SourcePruningEnumerationSelectedEdgeCoverage
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage''')
header=header.replace('''# Original resources through the captured-slot write

The selected edge supplies the actual returned native caller.
Finalization updates the enumeration cache and retains that caller.
The complete earlier history and resource bounds remain at the same endpoint.''','''# Constructive coverage through the actual captured-slot write

The accepted selected edge uses the original captured assignment value.
The selected-edge observer constructs that value at its actual native endpoint.
The original stored model supplies every inherited suspended restriction.
Finalization stores the same fragment and resets expansion ancestry.
The complete original resource and history packet remains available.''')
t=old[old.index('/-- Initial resources retain the full captured-slot history'):old.index('/-- Initial resources retain the complete earlier captured-slot interface')]
t=t.replace('/-- Initial resources retain the full captured-slot history and its actual native caller. -/','/-- An accepted captured assignment value constructs the actual finalized result with all original resources. -/',1)
t=t.replace('theorem complete_with_history_resources\n','theorem complete_with_history_resources_accepting\n',1)
needle='''        afterCaller.checked.native.machine.heap := by'''
observer='''        afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          result = .complete fragment afterCaller savedQueries after ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended after.core := by'''
assert t.count(needle)==1;t=t.replace(needle,observer,1)
t=t.replace('shape, returnedFits, returnedKnown⟩ :=','shape, returnedFits, returnedKnown, edgeAccepting⟩ :=',1)
t=t.replace('SourcePruningEnumerationSelectedEdge.complete_with_fragments_resources seed','SourcePruningEnumerationSelectedEdge.complete_with_fragments_resources_accepting seed',1)
marker='''  rcases shape with ⟨fragment, completed, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩ |'''
model='''  have edgeModel : ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (assignment : Nat → Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core →
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) →
      ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
        (∀ old < before.core.counter, extended old = assignment old) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended before.core ∧
        edgeResult = .complete fragment afterCaller savedQueries middle ∧
        Fragments.fill extended fragment = assignment uv ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended middle.core := by
    intro ambient assignment satisfied accepted
    have inherited : ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
      have model := satisfied.1.2 uv
      simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
        List.forall_mem_map] at model
      exact model.2
    obtain ⟨terms, termShape, childrenAccepted, guardHolds⟩ :=
      (InternedGuardedLanguage.edgeMeaning_all
        (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv)).mp accepted
    obtain ⟨extended, fragment, agree, originalSatisfied, completed, filled, middleSatisfied⟩ :=
      edgeAccepting ambient assignment terms satisfied childrenAccepted
        (by simpa only [termShape] using guardHolds)
        (by simpa only [termShape] using inherited)
    exact ⟨extended, fragment, agree, originalSatisfied, completed,
      filled.trans termShape.symm, middleSatisfied⟩
'''
assert marker in t;t=t.replace(marker,model+marker,1)
t=t.replace('''frame.root
  · subst edgeResult''','''frame.root
    · intro ambient assignment satisfied accepted
      obtain ⟨extended, produced, agree, originalSatisfied, completed, filled, middleSatisfied⟩ :=
        edgeModel ambient assignment satisfied accepted
      have producedSame : fragment = produced :=
        (SourcePruningEnumerationSelectedEdge.Result.complete.inj completed).1
      subst produced
      have selfValue : Fragments.fill extended fragment = extended uv :=
        filled.trans (agree uv ready.inside).symm
      refine ⟨extended, fragment, agree, originalSatisfied, rfl, filled, ?_⟩
      exact (SourcePruningEnumerationFinalize.written_semantics middle.core after.core uv fragment
        (List.getElem?_eq_some_iff.mp currentStored).1 core
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) extended).mpr
        ⟨EnumerationFrame.neutralize_satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended uv middle.core middleSatisfied, selfValue⟩
  · subst edgeResult''',1)
a1='''.inl ⟨fragment, rfl, afterSafe, ?_, finalStored, ?_, ?_, afterFragmentPending, advance⟩, returnedFits, returnedKnown⟩'''
b1='''.inl ⟨fragment, rfl, afterSafe, ?_, finalStored, ?_, ?_, afterFragmentPending, advance⟩, returnedFits, returnedKnown, ?_⟩'''
assert a1 in t;t=t.replace(a1,b1,1)
a2='''      .inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown⟩
    intro er en P H ek largeP largeH
    rw [run, edgeRun er en P H ek largeP largeH]'''
b2='''      .inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown, ?_⟩
    · intro er en P H ek largeP largeH
      rw [run, edgeRun er en P H ek largeP largeH]
    · intro ambient assignment satisfied accepted
      obtain ⟨extended, fragment, _agree, _originalSatisfied, impossible, _filled, _middleSatisfied⟩ :=
        edgeModel ambient assignment satisfied accepted
      cases impossible'''
assert a2 in t;t=t.replace(a2,b2,1)
s=header+t+'end MicroCFTA.SourcePruningEnumerationCapturedEdge\n'
out=a/'drafts/v1/SourcePruningEnumerationCapturedEdgeCoverage.lean';assert not out.exists();out.write_text(s)
def prop(s,name):
 i=s.index('theorem '+name+'\n');return s[i:s.index(' := by',i)]
oldp=prop(old,'complete_with_history_resources');newp=prop(s,'complete_with_history_resources_accepting')
recovered=newp[:newp.index(' ∧\n      ∀ (ambient : InternedGuardedLanguage.Env Symbol)')].replace('theorem complete_with_history_resources_accepting\n','theorem complete_with_history_resources\n',1)
assert oldp==recovered
cc=a/'contract-comparison';cc.mkdir(exist_ok=True)
for name,content in [('original-full-contract.lean.txt',oldp),('new-full-contract.lean.txt',newp),('recovered-old-full-contract.lean.txt',recovered)]:
 (cc/name).write_text(content)
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(cc/'comparison.json').write_text(json.dumps({'status':'PASS','recovery':'Remove only the final semantic observer and reverse the theorem name. ENTIRE old admission, witnesses and result prefix match literally.','original':ident(oldp.encode()),'new':ident(newp.encode()),'recovered':ident(recovered.encode())},indent=2)+'\n')
(a/'draft-status.json').write_text(json.dumps({'status':'UNTESTED','created_at':datetime.datetime.now().astimezone().isoformat(),'source':str(out),**ident(out.read_bytes()),'lines':len(s.splitlines()),'compiler_authority':'Root only'},indent=2)+'\n')
print(json.dumps({'source':str(out),**ident(out.read_bytes()),'lines':len(s.splitlines()),'old_contract':ident(oldp.encode())},indent=2))
