from pathlib import Path
import json
r=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');a=Path('/tmp/mcfta-prepared-composition-20261028');s=(r/'SourcePruningEnumerationPreparedFiniteSiblingOrigins.lean').read_text()
head=s[:s.index('/-- A supported indexed prefix')]
head='import MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingOrigins\nimport MicroCFTA.SourcePruningEnumerationSelectorLanguage\n\n'+head[head.index('namespace '):]
decl=s[s.index('theorem alternatives_finite_complete_resources_origins'):s.index(' := by\n')]
decl=decl.replace('theorem alternatives_finite_complete_resources_origins','theorem parent_finite_complete_resources_origins',1)
decl=decl.replace('    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)','''    (selectedRows : selectedEdges.Perm storedEdges)
    (supported : ∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none)''',1)
marker='      (∀ extra, SourcePruningEnumerationNativeContinuations.run'
start=decl.index(marker);params=decl[:start];oldResult=decl[start:]
# The complete original uniform sibling observer is retained first.
newPrefix='''      ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol)
        (whole : Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient
          (.node parentEntry storedEdges depth free) (assignment uv) →
        AssignmentOrigins whole before.core.counter assignment →
        ∃ (index : Nat) (chosen : EdgeValue Symbol Constraint),
          selectedEdges[index]? = some chosen ∧
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient chosen (assignment uv) ∧
          ∀ extra,
            let work := bound + extra
            let hook := continueWith
              (resume holeKey fits admits graph templates checkEmpty edgesOf stop order work recursiveFuel)
              graph templates stop order work metadata uv
'''
event=oldResult[oldResult.index('            ∃ (eventIndex'):]
body=''' := by
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result, retained⟩ :=
    alternatives_finite_complete_resources_origins
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver inventory caller memos before uv handle scs parentEntry storedEdges selectedEdges
      depth free packet ready stored parentAvailable parentClosed
      (fun edge member => selectedRows.mem_iff.mp member) incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, processed, outputs, afterCaller, next, final, result, retained, ?_⟩
  intro ambient assignment whole satisfied parentAccepted origins
  obtain ⟨chosen, offered, _member, _resident, accepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap packet.context.ready.semantic.ready parentEntry storedEdges
      selectedEdges depth free parentAvailable selectedRows (SourceEqualityPCSGuard.holds formulas solver)
      ambient (assignment uv) parentAccepted
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp offered
  have prefixSupported : ∀ earlier ∈ selectedEdges.take index,
      arityAllows earlier.children.length scs = true →
      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
    intro earlier member allowed
    exact supported earlier (List.mem_of_mem_take member) allowed
  obtain ⟨_running, _post, _captured, _fits, _known, _length, _receipts, _outputs, _shape, accepting⟩ := retained
  refine ⟨index, chosen, found, accepted, ?_⟩
  intro extra
  exact accepting extra index chosen found prefixSupported ambient assignment whole satisfied accepted origins

end MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources
'''
text=head+'''/-- An accepted prepared parent derives its indexed origin-aware event in the actual sibling scan. -/
'''+params+'      ('+oldResult.strip()+') ∧\n'+newPrefix+event+body
m='SourcePruningEnumerationPreparedFiniteParentOrigins';(r/(m+'.lean')).write_text(text)
v=json.loads((a/'modules.json').read_text());v.append(m);(a/'modules.json').write_text(json.dumps(v,indent=2)+'\n')
print(m,len(text.encode()))
