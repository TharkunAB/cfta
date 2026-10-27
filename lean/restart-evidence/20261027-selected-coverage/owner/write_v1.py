from pathlib import Path
import hashlib,json,datetime
root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-selected-coverage-20261027/owner')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeResources.lean').read_text()
header=old[:old.index('/-- Count the original mixed reservation')]
header=header.replace('import MicroCFTA.SourcePruningEnumerationSelectedEdge\nimport MicroCFTA.SourcePruningEnumerationTraversalResources', '''import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources
import MicroCFTA.SourcePruningEnumerationTraversalCoverage
import MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeFinishLanguage
import MicroCFTA.SourcePruningEnumerationAnnotationHeap
import MicroCFTA.EnumerationSuspendedForward''')
header=header.replace('''# Original resources through the actual selected edge

The projected classes determine the actual ordered child buckets.
Their full lengths include inherited and fresh own-class entries.
One original reservation covers every reached child.
The residual update retains the returned native caller.''','''# Constructive coverage of the actual selected edge

The current annotation heap supplies the exact projected guard meaning.
Fresh witnesses preserve every variable in the original state.
The ordered traversal constructs the accepted children at its own endpoint.
The residual write uses the actual native guard interpretation.
The full original resource packet remains available.''')
header += 'variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]\n\n'
start=old.index('/-- Original resources retain')
end=old.index('/-- The complete resource interface')
theorem=old[start:end]
theorem=theorem.replace('/-- Original resources retain the full selected-edge fragment packet and its returned caller. -/','/-- An accepted selected-edge model constructs the same completed result with all original resources. -/')
theorem=theorem.replace('theorem complete_with_fragments_resources\n','theorem complete_with_fragments_resources_accepting\n',1)
needle='''        afterCaller.checked.native.machine.heap := by'''
observer='''        afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol) (terms : List (Language.Term Symbol)),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient) edge.children terms →
        SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint
          (.node edge.entry.key.symbol terms) = true →
        (∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          result = .complete fragment afterCaller savedQueries after ∧
          Fragments.fill extended fragment = .node edge.entry.key.symbol terms ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended after.core := by'''
assert theorem.count(needle)==1
theorem=theorem.replace(needle,observer)
theorem=theorem.replace('shape, returnedFits, returnedKnown⟩ :=','shape, returnedFits, returnedKnown, childrenAccepting⟩ :=',1)
theorem=theorem.replace('SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources seed','SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_accepting seed',1)
marker='  have ownOrigin : EnumeratedOrigin before.core own.core := by\n'
model='''  have model : ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (assignment : Nat → Language.Term Symbol) (terms : List (Language.Term Symbol)),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core →
      Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient) edge.children terms →
      SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint
        (.node edge.entry.key.symbol terms) = true →
      (∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →
      ∃ extended : Nat → Language.Term Symbol,
        (∀ uv < before.core.counter, extended uv = assignment uv) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended before.core ∧
        childResult = .complete fragments afterCaller savedQueries after ∧
        fragments.map (Fragments.fill extended) = terms ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended after.core ∧
        ResidualHolds
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          residual (.node edge.entry.key.symbol terms) := by
    intro ambient assignment terms satisfied accepted guardHolds inherited
    obtain ⟨_validTries, projectionMeaning⟩ :=
      SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
        caller.checked.native.machine.heap parentEntry edges depth free edge
        initial.ready.semantic.ready initial.annotation_heap parentAvailable selected tries residual projected
    obtain ⟨equalities, residualHolds⟩ := (projectionMeaning formulas solver _).mp guardHolds
    obtain ⟨witnesses, ownSatisfied, freshAgree, freshHolds⟩ :=
      fresh_classes_state_complete
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        before.core safe.1 assignment satisfied (.node edge.entry.key.symbol terms) tries equalities
    rw [← ownCore] at ownSatisfied
    have combinedHolds : ∀ sc ∈ scs ++ suspendedVars before.core.counter tries,
        Suspended.Holds witnesses (.node edge.entry.key.symbol terms) sc := by
      intro sc member
      rcases List.mem_append.mp member with old | fresh
      · exact EnumerationConstruction.holds_extension assignment witnesses before.core.counter
          freshAgree sc (bounded sc old) _ (inherited sc old)
      · exact freshHolds sc fresh
    have descended := suspended_descent_forward witnesses edge.entry.key.symbol terms
      (scs ++ suspendedVars before.core.counter tries) combinedHolds
    have indexed : ∀ (nodes : List Node) (values : List (Language.Term Symbol)),
        Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient) nodes values →
        ∀ start,
          (∀ index child, values[index]? = some child →
            ∀ sc ∈ descendScs (start + index) (scs ++ suspendedVars before.core.counter tries),
              Suspended.Holds witnesses child sc) →
          Language.All₂ (fun indexed child =>
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient indexed.1 child ∧
            ∀ sc ∈ descendScs indexed.2 (scs ++ suspendedVars before.core.counter tries),
              Suspended.Holds witnesses child sc) (nodes.zipIdx start) values := by
      intro nodes values related
      induction related with
      | nil => intro start _; exact .nil
      | cons head tail ih =>
          intro start holds
          simp only [List.zipIdx_cons]
          apply Language.All₂.cons
          · exact ⟨head, by simpa only [Nat.add_zero] using holds 0 _ rfl⟩
          · apply ih (start + 1)
            intro index child found
            have evidence := holds (index + 1) child found
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using evidence
    have indexedModels := indexed edge.children terms accepted 0 (by simpa only [Nat.zero_add] using descended)
    have inputModels : Language.All₂ (fun input term =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds witnesses term sc) inputs terms := by
      have mapped := EnumerationSemantics.all₂_map_both
        (fun indexed : Node × Nat => (indexed.1,
          descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.core.counter tries)))
        id _ _ (fun _ _ evidence => evidence) edge.children.zipIdx terms indexedModels
      simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.map_id,
        descendScs, EqualityTrie.descendScs, List.map_append, List.filter_append] using mapped
    obtain ⟨extended, childAgree, _ownOriginalSatisfied, completed, filled, afterSatisfied⟩ :=
      childrenAccepting ambient
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        witnesses terms ownSatisfied inputModels
    have agree : ∀ uv < before.core.counter, extended uv = assignment uv := by
      intro uv inside
      exact (childAgree uv (by omega)).trans (freshAgree uv inside)
    have originalSatisfied := (state_assignment_congr
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      before.core safe.1 extended assignment agree).mpr satisfied
    exact ⟨extended, agree, originalSatisfied, completed, filled, afterSatisfied, residualHolds⟩
'''
assert marker in theorem
theorem=theorem.replace(marker,model+marker,1)
theorem=theorem.replace('''    have fragmentBound : FragmentBound after.core.counter fragment := node_bound_resources _ _ _ fragmentBounds''','''    have fragmentBound : FragmentBound after.core.counter fragment := by
      have build : ∀ fragments : List Fragment,
          (∀ child ∈ fragments, FragmentBound after.core.counter child) →
          FragmentBound after.core.counter (.node edge.entry.key.symbol fragments) := by
        intro children childrenBound
        induction children with
        | nil => trivial
        | cons child rest ih =>
            exact ⟨childrenBound child (by simp), ih (fun item member => childrenBound item (by simp [member]))⟩
      exact build fragments fragmentBounds''')
theorem=theorem.replace('''      returnedFits, returnedKnown⟩
    · intro er''','''      returnedFits, returnedKnown, ?_⟩
    · intro er''',1)
marker='''      exact frame.trans (finish_protected residual fragment after held frame.root)
  · subst childResult'''
replacement='''      exact frame.trans (finish_protected residual fragment after held frame.root)
    · intro ambient assignment terms satisfied accepted guardHolds inherited
      obtain ⟨extended, agree, originalSatisfied, _completed, filled, afterSatisfied, residualHolds⟩ :=
        model ambient assignment terms satisfied accepted guardHolds inherited
      have termSame : Fragments.fill extended fragment = .node edge.entry.key.symbol terms := by
        simp only [fragment, Fragments.fill, filled]
      refine ⟨extended, fragment, agree, originalSatisfied, rfl, termSame, ?_⟩
      exact (finish_semantics residual fragment after
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) extended).mpr
        ⟨afterSatisfied, by simpa only [termSame] using residualHolds⟩
  · subst childResult'''
assert marker in theorem
theorem=theorem.replace(marker,replacement,1)
theorem=theorem.replace('''.inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown⟩''','''.inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown, ?_⟩''',1)
theorem=theorem.rstrip()+'''
    · intro ambient assignment terms satisfied accepted guardHolds inherited
      obtain ⟨extended, _agree, _originalSatisfied, impossible, _filled, _afterSatisfied, _residualHolds⟩ :=
        model ambient assignment terms satisfied accepted guardHolds inherited
      cases impossible

end MicroCFTA.SourcePruningEnumerationSelectedEdge
'''
text=header+theorem
out=area/'drafts/v1/SourcePruningEnumerationSelectedEdgeCoverage.lean'
out.parent.mkdir(parents=True,exist_ok=True)
assert not out.exists()
out.write_text(text)
oldstmt=old[old.index('theorem complete_with_fragments_resources\n'):old.index(' := by',old.index('theorem complete_with_fragments_resources\n'))]
newstmt=text[text.index('theorem complete_with_fragments_resources_accepting\n'):text.index(' := by',text.index('theorem complete_with_fragments_resources_accepting\n'))]
recovered=newstmt[:newstmt.index(' ∧\n      ∀ (ambient : InternedGuardedLanguage.Env Symbol)')].replace('theorem complete_with_fragments_resources_accepting\n','theorem complete_with_fragments_resources\n',1)
assert oldstmt==recovered
(area/'contract-comparison').mkdir(exist_ok=True)
for name,value in [('original-full-contract.lean.txt',oldstmt),('new-full-contract.lean.txt',newstmt),('recovered-old-full-contract.lean.txt',recovered)]:
 (area/'contract-comparison'/name).write_text(value)
def ident(b):return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
(area/'contract-comparison/comparison.json').write_text(json.dumps({'status':'PASS','recovery':'Remove only final semantic observer and reverse theorem name. Full original admission and existential/conclusion packet match literally.','original':ident(oldstmt.encode()),'new':ident(newstmt.encode()),'recovered':ident(recovered.encode())},indent=2)+'\n')
(area/'draft-status.json').write_text(json.dumps({'status':'UNTESTED','source':str(out),'source_identity':ident(out.read_bytes()),'lines':len(text.splitlines()),'compiler_authority':'Root only','draft_created':datetime.datetime.now().astimezone().isoformat()},indent=2)+'\n')
print(json.dumps({'draft':str(out),'lines':len(text.splitlines()),**ident(out.read_bytes()),'old_contract':ident(oldstmt.encode())},indent=2))
