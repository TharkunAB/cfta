from pathlib import Path
import json,hashlib,datetime
root=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-native-scan-coverage-20261027/head-owner')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean').read_text()
header=old[:old.index('/-- Count the original projected child cost')]
header=header.replace('import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion\nimport MicroCFTA.SourcePruningEnumerationCapturedEdgeResources','''import MicroCFTA.SourcePruningEnumerationNativeBranchResources
import MicroCFTA.SourcePruningEnumerationCapturedEdgeCoverage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission''')
header=header.replace('''# Original resources through ordered native alternatives

Each alternative uses the same captured enumeration cache.
Its actual returned caller and queries pass to the next alternative.
The original projected buckets determine every reserved mixed query step.
Each processed receipt retains bounds for its own exact selected-edge prefix.''','''# Constructive coverage of one actual native alternative

The original stored model supplies each inherited restriction.
Selected-edge acceptance excludes unsupported projection and arity rejection.
The supported branch constructs the actual captured completion.
The full original head resource packet remains available.
Operational bounds precede the universal semantic observer.''')
header+='variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]\n\n'
t=old[old.index('/-- Original resources derive one actual native alternative'):old.index('/-- Original resources retain all receipt histories')]
t=t.replace('/-- Original resources derive one actual native alternative and its complete receipt. -/','/-- An accepted captured assignment value constructs this actual native head receipt. -/',1)
t=t.replace('theorem head_complete_resources\n','theorem head_complete_resources_accepting\n',1)
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
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (afterCache : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          receipt = .complete fragment afterCaller saved afterCache ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended afterCache.core := by
  have acceptedChecks : ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (assignment : Nat → Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core →
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) →
      arityAllows edge.children.length scs = true ∧
        ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) := by
    intro ambient assignment satisfied accepted
    obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
    have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
    subst value
    have slotModel := satisfied.1.2 uv
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
      List.forall_mem_map] at slotModel
    obtain ⟨tries, residual, _terms, projected, _valid, _termShape, _children,
      _length, allowed, _ownEqualities, _residualHolds⟩ :=
      SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
        parentEntry edges depth free edge scs initial available selected ambient assignment
        (assignment uv) accepted slotModel.2
    exact ⟨allowed, tries, residual, projected⟩'''
assert needle in t;t=t.replace(needle,observer,1)
t=t.replace('''          ?_, ?_⟩
        · intro er''','''          ?_, ?_, ?_⟩
        · intro er''',1)
marker='''        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known
    | some pair =>'''
replacement='''        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known
        · intro ambient assignment satisfied accepted
          obtain ⟨_allowed, tries, residual, actualProjected⟩ :=
            acceptedChecks ambient assignment satisfied accepted
          rw [projected] at actualProjected
          cases actualProjected
    | some pair =>'''
assert marker in t;t=t.replace(marker,replacement,1)
t=t.replace('shape, returnedFits, returnedKnown⟩ :=','shape, returnedFits, returnedKnown, accepting⟩ :=',1)
t=t.replace('SourcePruningEnumerationCapturedEdge.complete_with_history_resources seed','SourcePruningEnumerationCapturedEdge.complete_with_history_resources_accepting seed',1)
marker='''          exact ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            ⟨valid, safe, bounded, written, ancestry, root⟩, pendingHistory, ⟨growth, fragmentPending, ordered⟩,
            .inl rfl, headFits, headKnown⟩'''
replacement='''          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            ⟨valid, safe, bounded, written, ancestry, root⟩, pendingHistory, ⟨growth, fragmentPending, ordered⟩,
            .inl rfl, headFits, headKnown, ?_⟩
          intro ambient assignment satisfied accepted
          obtain ⟨extended, produced, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
            accepting ambient assignment satisfied accepted
          exact ⟨extended, produced, after, agree, originalSatisfied, completed, filled, afterSatisfied⟩'''
assert marker in t;t=t.replace(marker,replacement,1)
marker='''          exact ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            valid, pendingHistory, trivial, .inl rfl, headFits, headKnown⟩'''
replacement='''          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            valid, pendingHistory, trivial, .inl rfl, headFits, headKnown, ?_⟩
          intro ambient assignment satisfied accepted
          obtain ⟨extended, produced, _agree, _originalSatisfied, impossible, _filled, _afterSatisfied⟩ :=
            accepting ambient assignment satisfied accepted
          cases impossible'''
assert marker in t;t=t.replace(marker,replacement,1)
marker='''      (fun history _ => history), trivial, .inl rfl, ?_, ?_⟩'''
replacement='''      (fun history _ => history), trivial, .inl rfl, ?_, ?_, ?_⟩'''
assert marker in t;t=t.replace(marker,replacement,1)
t=t.rstrip()+'''
    · intro ambient assignment satisfied accepted
      obtain ⟨actualAllowed, _tries, _residual, _projected⟩ :=
        acceptedChecks ambient assignment satisfied accepted
      exact (allowed actualAllowed).elim

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
'''
s=header+t;out=a/'drafts/v1/SourcePruningEnumerationNativeHeadCoverage.lean';assert not out.exists();out.write_text(s)
def prop(s,name):
 i=s.index('theorem '+name+'\n');return s[i:s.index(' := by',i)]
oldp=prop(old,'head_complete_resources');newp=prop(s,'head_complete_resources_accepting')
recovered=newp[:newp.index(' ∧\n      ∀ (ambient : InternedGuardedLanguage.Env Symbol)')].replace('theorem head_complete_resources_accepting\n','theorem head_complete_resources\n',1)
assert recovered==oldp
cc=a/'contract-comparison';cc.mkdir(exist_ok=True)
for name,content in [('original-full-contract.txt',oldp),('new-full-contract.txt',newp),('recovered-old-full-contract.txt',recovered)]:
 (cc/name).write_text(content)
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(cc/'comparison.json').write_text(json.dumps({'status':'PASS','recovery':'Delete only the final observer and restore the original theorem name. ENTIRE original admission, witnesses and result prefix match literally.','original':ident(oldp.encode()),'new':ident(newp.encode()),'recovered':ident(recovered.encode())},indent=2)+'\n')
(a/'draft-status.json').write_text(json.dumps({'status':'UNTESTED','created_at':datetime.datetime.now().astimezone().isoformat(),'source':str(out),**ident(out.read_bytes()),'lines':len(s.splitlines()),'compiler_authority':'Root only'},indent=2)+'\n')
print(json.dumps({'source':str(out),**ident(out.read_bytes()),'lines':len(s.splitlines()),'old_contract':ident(oldp.encode())},indent=2))
