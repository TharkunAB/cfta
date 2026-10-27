from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-selector-capture-20261027')
source = (root / 'lean/MicroCFTA/SourcePruningEnumerationCapturedEdgeCoverage.lean').read_text()
name = 'complete_with_history_resources_accepting'
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
arguments = arguments.replace('    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat)',
    '    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (roots : Nat → Nat)')
old_selected = '    (selected : edge ∈ edges)\n'
assert arguments.count(old_selected) == 1
arguments = arguments.replace(old_selected,
    '    (selectedRows : (edgesOf (.node parentEntry edges depth free)).Perm edges)\n')
old_reservation = '    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))\n'
assert arguments.count(old_reservation) == 1
arguments = arguments.replace(old_reservation, '''    (reserved : ∀ edge ∈ edgesOf (.node parentEntry edges depth free),
      ∀ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
''')
parameters = '''
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)'''
header, rest = result.split(',\n      (∀ er en P H ek', 1)
packet = '(∀ er en P H ek' + rest
completion = '''      ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
        (∀ old < before.core.counter, extended old = assignment old) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended before.core ∧
        result = .complete fragment afterCaller savedQueries after ∧
        Fragments.fill extended fragment = assignment uv ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended after.core'''
proof = ''' := by
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have model := satisfied.1.2 uv
  simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
    List.forall_mem_map] at model
  have parentAccepted : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient
      (.node parentEntry edges depth free) (assignment uv) :=
    (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp model.1
  obtain ⟨edge, offered, selected, _resident, accepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap initial.ready.semantic.ready parentEntry edges
      (edgesOf (.node parentEntry edges depth free)) depth free available selectedRows
      (SourceEqualityPCSGuard.holds formulas solver) ambient (assignment uv) parentAccepted
  obtain ⟨tries, residual, _terms, projected, _valid, _termShape, _childrenAccepted,
    _length, allowed, _ownEqualities, _residualHolds⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry edges depth free edge scs initial available selected ambient assignment
      (assignment uv) accepted model.2
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, pendingInputs, protects, pendingHistory, shape, returnedFits, returnedKnown, accepting⟩ :=
    complete_with_history_resources_accepting seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded
      realized selected paths counts flags pending allowed tries residual projected fits
      (reserved edge offered tries residual projected) known
  obtain ⟨extended, fragment, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
    accepting ambient assignment satisfied accepted
  refine ⟨edge, offered, selected, tries, residual, projected, allowed, r, n, p, h, k,
    afterCaller, after, savedQueries, final, next, afterRoots, result, ?_,
    extended, fragment, agree, originalSatisfied, completed, filled, afterSatisfied⟩
  exact ⟨running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
    afterFlags, origin, pendingInputs, protects, pendingHistory, shape, returnedFits,
    returnedKnown, accepting⟩

end MicroCFTA.SourcePruningEnumerationCapturedEdge
'''
namespace = source[source.index('namespace MicroCFTA.'):source.index('/-- An accepted captured assignment')]
intro = '''import MicroCFTA.SourcePruningEnumerationCapturedEdgeCoverage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission
import MicroCFTA.SourcePruningEnumerationSelectorLanguage

/-!
# Captured completion from an original ordinary-parent model

The original stored model supplies parent acceptance and suspended constraints.
A permutation selector retains an accepting resident edge.
Native acceptance derives its actual projection and arity precheck.
The same captured call constructs a finalized satisfying extension.
Its complete resource packet and uniform semantic observer remain available.
This result does not assert that an ordered scan reaches the selected edge.
-/
'''
text = intro + namespace + '''/-- An original parent model supplies a selected edge and its actual completed captured result. -/
theorem selected_parent_complete''' + arguments + parameters + ''' :
    ∃ edge, edge ∈ edgesOf (.node parentEntry edges depth free) ∧ edge ∈ edges ∧
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      arityAllows edge.children.length scs = true ∧
''' + header + ',\n      (' + packet + ') ∧\n' + completion + proof
path = area / 'captured-accepted/drafts/v1/SourcePruningEnumerationCapturedEdgeAccepting.lean'
assert not path.exists()
path.parent.mkdir(parents=True)
path.write_text(text)
record = dict(draft=str(path), bytes=len(text.encode()), lines=len(text.splitlines()),
    sha256=hashlib.sha256(text.encode()).hexdigest(),
    producer_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
    retains_entire_strengthened_resource_packet=True,
    supplied_edge_acceptance_projection_arity_inherited_removed=True,
    reservation='All currently selected edges and each unique current successful pure projection; no future heap or execution.',
    quantifiers='Chosen original satisfying model precedes selected edge and runtime bounds; the full inner uniform observer follows those bounds.')
(area / 'captured-accepted/draft-v1.json').write_text(json.dumps(record, indent=2) + '\n')
(area / 'captured-accepted/compose-draft.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(record))
