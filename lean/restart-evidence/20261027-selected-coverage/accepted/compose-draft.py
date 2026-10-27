from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-selected-coverage-20261027')
source = (root / 'lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeCoverage.lean').read_text()
name = 'complete_with_fragments_resources_accepting'
start = source.index('theorem ' + name)
statement = source[start:source.index(' := by\n', start)]
arguments, result = statement[len('theorem ' + name):].split(' :\n    ∃ (r n p h k', 1)
result = '    ∃ (r n p h k' + result
removed = '''    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
'''
assert arguments.count(removed) == 1
arguments = arguments.replace(removed, '')
old_reservation = '    (reserved : Reserved bits seed (cost edge scs before.core.counter tries))\n'
assert arguments.count(old_reservation) == 1
arguments = arguments.replace(old_reservation, '''    (reserved : ∀ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      Reserved bits seed (cost edge scs before.core.counter tries))
''')
parameters = '''
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Language.Term Symbol) (term : Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc)'''
header, rest = result.split(',\n      (∀ er en P H ek', 1)
packet = '(∀ er en P H ek' + rest
completion = '''      ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
        (∀ uv < before.core.counter, extended uv = assignment uv) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended before.core ∧
        result = .complete fragment afterCaller savedQueries after ∧
        Fragments.fill extended fragment = term ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended after.core'''
proof = ''' := by
  obtain ⟨tries, residual, terms, projected, _valid, termShape, childrenAccepted,
    _length, allowed, _ownEqualities, _residualHolds⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry edges depth free edge scs initial parentAvailable selected ambient assignment term accepted inherited
  obtain ⟨_terms, _shape, _children, guardHolds⟩ :=
    (InternedGuardedLanguage.edgeMeaning_all
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term).mp accepted
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, pendingInputs, protects, pendingHistory, incomingHistory, shape, returnedFits,
    returnedKnown, accepting⟩ :=
    complete_with_fragments_resources_accepting seed formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial parentAvailable parentClosed selected
      safe realized paths counts flags bounded pending allowed tries residual projected fits
      (reserved tries residual projected) known
  obtain ⟨extended, fragment, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
    accepting ambient assignment terms satisfied childrenAccepted
      (by simpa only [termShape] using guardHolds)
      (by simpa only [termShape] using inherited)
  refine ⟨tries, residual, projected, allowed, r, n, p, h, k, afterCaller, after, savedQueries,
    final, next, afterRoots, result, ?_, extended, fragment, agree, originalSatisfied, completed, ?_, afterSatisfied⟩
  · exact ⟨running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
      afterFlags, origin, pendingInputs, protects, pendingHistory, incomingHistory, shape,
      returnedFits, returnedKnown, accepting⟩
  · simpa only [termShape] using filled

end MicroCFTA.SourcePruningEnumerationSelectedEdge
'''
namespace = source[source.index('namespace MicroCFTA.'):source.index('/-- An accepted selected-edge model')]
intro = '''import MicroCFTA.SourcePruningEnumerationSelectedEdgeCoverage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission

/-!
# Completion from an accepted current selected edge

Native acceptance derives the actual projection and inherited arity check.
The original resource reservation covers that unique current projection.
The complete resource packet and its uniform semantic observer remain.
An accepted model constructs the actual completed symbolic edge fragment.
-/
'''
text = intro + namespace + '''/-- An accepted native edge derives its prechecks and constructs its actual completed fragment. -/
theorem accepted_complete''' + arguments + parameters + ''' :
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      arityAllows edge.children.length scs = true ∧
''' + header + ',\n      (' + packet + ') ∧\n' + completion + proof
path = area / 'accepted/drafts/v1/SourcePruningEnumerationSelectedEdgeAccepting.lean'
assert not path.exists()
path.parent.mkdir(parents=True)
path.write_text(text)
record = dict(draft=str(path), bytes=len(text.encode()), lines=len(text.splitlines()),
              sha256=hashlib.sha256(text.encode()).hexdigest(),
              producer_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
              retains_entire_strengthened_resource_packet=True,
              given_projection_and_arity_removed=True,
              reservation='Conditional on unique actual current pure projection; no future heap or execution.',
              quantifiers='Semantic-facing accepted model precedes existential bounds. Preserved inner producer packet retains its uniform observer after bounds.')
(area / 'accepted/draft-v1.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
