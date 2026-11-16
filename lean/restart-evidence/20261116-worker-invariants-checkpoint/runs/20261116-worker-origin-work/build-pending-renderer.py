from pathlib import Path
import hashlib
import json

root=Path('/home/tritlo/Code/mcfta');packet=root/'lean/restart-evidence/20261116-current-pending-native-rendering-draft'
old=(root/'lean/MicroCFTA/SourcePruningEnumerationRendering.lean').read_text()
header=(packet/'PUBLIC-HEADER.lean.txt').read_text()
assert hashlib.sha256(header.encode()).hexdigest()==json.loads((packet/'FROZEN-HEADER.json').read_text())['header_sha256']
start=old.index('private def Valid');stop=old.index('/-- Structural completion')
helpers=old[start:stop]
helpers=helpers.replace('(assignment : Nat → Term Symbol)\n    (state', '(assignment : Nat → Term Symbol) (marker : Symbol)\n    (state')
helpers=helpers.replace('∧ Discharged state', '''∧
      ∀ (uv : Nat) (node : Option Nat) (scs : List Suspended),
        state.values[uv]? = some (.unenumerated node scs) → assignment uv = .node marker []''')
helpers=helpers.replace('Valid language assignment ', 'Valid language assignment marker ')
helpers=helpers.replace('private theorem read_sound (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol)\n',
 'private theorem read_sound (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)\n')
helpers=helpers.replace('node = none ∧ scs = []) := by', 'assignment uv = .node marker []) := by')
helpers=helpers.replace('read_sound language assignment\n', 'read_sound language assignment marker\n')
helpers=helpers.replace('exact valid.2.2 root node scs (by simpa only [same] using stored)',
 'exact assigned.trans (valid.2.2 root node scs (by simpa only [same] using stored))')
fragment_old='''          | unenumerated node scs =>
              obtain ⟨rfl, rfl⟩ := free node scs rfl
              exact (success_failure .unfinishedFragment middle after term continued).elim'''
fragment_new='''          | unenumerated node scs =>
              have chosen := free node scs rfl
              cases node with
              | none => exact (success_failure .unfinishedFragment middle after term continued).elim
              | some handle =>
                  cases decoded : lookupNode heap handle with
                  | none =>
                      simp only [decoded] at continued
                      exact (success_failure .unresolvedReference middle after term continued).elim
                  | some value =>
                      simp only [decoded] at continued
                      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
                      · simp only [ite_eq_left boundary] at continued
                        obtain ⟨rfl, rfl⟩ := (success_pure (.node marker []) term middle after).mp continued
                        exact ⟨readValid, frame, by simpa only [fill] using chosen.symm⟩
                      · simp only [ite_eq_right boundary] at continued
                        exact (success_failure .unfinishedFragment middle after term continued).elim'''
assert helpers.count(fragment_old)==1;helpers=helpers.replace(fragment_old,fragment_new)
root_old='''  | unenumerated node scs =>
      obtain ⟨rfl, rfl⟩ := free node scs rfl
      exact (reject_unsuccessful middle after term continued).elim'''
root_new='''  | unenumerated node scs =>
      have chosen := free node scs rfl
      cases node with
      | none => exact (reject_unsuccessful middle after term continued).elim
      | some handle =>
          cases decoded : lookupNode heap handle with
          | none =>
              simp only [decoded] at continued
              exact (success_failure .unresolvedReference middle after term continued).elim
          | some value =>
              simp only [decoded] at continued
              by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
              · simp only [ite_eq_left boundary] at continued
                obtain ⟨rfl, rfl⟩ := (success_pure (.node marker []) term middle after).mp continued
                exact ⟨readValid, frame, chosen.symm⟩
              · simp only [ite_eq_right boundary] at continued
                exact (reject_unsuccessful middle after term continued).elim'''
assert helpers.count(root_old)==1;helpers=helpers.replace(root_old,root_new)
render=old[old.index(' := by',old.index('theorem render_assignment')):old.index('\nend MicroCFTA.SourcePruningEnumerationRendering')]
render=render.replace('obtain ⟨assignment, equations⟩ := EnumerationAssignment.stratified_assignment',
 'obtain ⟨assignment, equations, chosen⟩ := EnumerationPendingAssignment.stratified_pending_assignment')
render=render.replace('language discharged','language choices').replace('equations, discharged','equations, chosen')
render=render.replace('Valid language assignment ', 'Valid language assignment marker ')
source=(packet/'PREAMBLE.lean.txt').read_text()+helpers+header+render+'\n\nend MicroCFTA.SourcePruningEnumerationPendingRendering\n'
assert header in source and 'Discharged' not in source and 'discharged' not in source
target=packet/'SourcePruningEnumerationPendingRendering.lean';assert not target.exists();target.write_text(source)
print(json.dumps({'source':str(target),'lines':len(source.splitlines()),'sha256':hashlib.sha256(source.encode()).hexdigest(),
 'original_renderer_source_unchanged':True,'public_header_exact':True,'uncompiled':True}))
