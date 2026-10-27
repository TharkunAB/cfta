from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-scan-coverage-20261027')
source = (root / 'lean/MicroCFTA/SourcePruningEnumerationNativeBranchCoverage.lean').read_text()
name = 'complete_with_history_resources_accepting'
start = source.index('theorem ' + name)
statement = source[start:source.index(' := by\n', start)]
arguments, result = statement[len('theorem ' + name):].split(' :\n    ∃ (r n p h k', 1)
result = '    ∃ (r n p h k' + result
old_selected = '    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)\n'
assert arguments.count(old_selected) == 1
arguments = arguments.replace(old_selected, '''    (selectedRows : selectedEdges.Perm storedEdges)
    (supported : ∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none)
''')
parameters = '''
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment before.core)'''
header, rest = result.split(',\n      (∀ er en P H ek', 1)
packet = '(∀ er en P H ek' + rest
observer = statement[statement.index('      ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint),'):]
chosen_result = observer[observer.index('          ∃ (headCaller :'):]
proof = ''' := by
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry storedEdges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have model := satisfied.1.2 uv
  simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
    List.forall_mem_map] at model
  have parentAccepted : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient
      (.node parentEntry storedEdges depth free) (assignment uv) :=
    (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp model.1
  obtain ⟨chosen, offered, _member, _resident, accepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap initial.ready.semantic.ready parentEntry storedEdges
      selectedEdges depth free available selectedRows (SourceEqualityPCSGuard.holds formulas solver)
      ambient (assignment uv) parentAccepted
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp offered
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    running, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory,
    shape, allSupported, returnedFits, returnedKnown, indexedResources, accepting⟩ :=
    complete_with_history_resources_accepting seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry storedEdges selectedEdges depth free roots memos initial ready stored
      decoded realized (fun edge member => selectedRows.mem_iff.mp member) paths counts flags pending
      fits reserved known
  have prefixSupported : ∀ earlier ∈ selectedEdges.take index,
      arityAllows earlier.children.length scs = true →
      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
    intro earlier member allowed
    exact supported earlier (List.mem_of_mem_take member) allowed
  obtain ⟨headCaller, headInventory, headMemos, branchCaller, branchQueries, branchMemos,
    branchInventory, afterCache, extended, fragment, inputPost, branchPost, branchQuery,
    selectedReceipt, selectedRun, agree, oldSatisfied, filled, afterSatisfied⟩ :=
    accepting index chosen found prefixSupported ambient assignment satisfied accepted
  refine ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result, ?_,
    allSupported supported, index, chosen, found, headCaller, headInventory, headMemos,
    branchCaller, branchQueries, branchMemos, branchInventory, afterCache, extended, fragment,
    inputPost, branchPost, branchQuery, selectedReceipt, selectedRun, agree, oldSatisfied,
    filled, afterSatisfied⟩
  exact ⟨running, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory,
    shape, allSupported, returnedFits, returnedKnown, indexedResources, accepting⟩

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
'''
namespace = source[source.index('namespace MicroCFTA.'):source.index('/-- A supported prefix')]
intro = '''import MicroCFTA.SourcePruningEnumerationNativeBranchCoverage
import MicroCFTA.SourcePruningEnumerationSelectorLanguage

/-!
# A supported native scan constructs the original parent value

The original satisfying stored model supplies an accepting selected edge.
A permutation selector retains that edge at an actual list index.
Original support for the full selected list excludes unsupported prefixes.
The same complete native scan contains the actual completed chosen receipt.
The chosen branch keeps its own caller, full memo states and final cache.
The complete primary resource packet and its uniform observer remain.
This theorem does not cover earlier recursive continuation stops.
-/
'''
text = intro + namespace + '''/-- An original parent model constructs a completed indexed receipt in the same supported scan. -/
theorem parent_complete_resources''' + arguments + parameters + ' :\n' + header + ',\n      (' + packet + ''') ∧
      result = .complete processed afterCaller saved ∧
      ∃ (index : Nat) (chosen : EdgeValue Symbol Constraint),
        selectedEdges[index]? = some chosen ∧
''' + chosen_result + proof
path = area / 'parent/drafts/v1/SourcePruningEnumerationNativeParentCoverage.lean'
assert not path.exists()
path.parent.mkdir(parents=True)
path.write_text(text)
(area / 'parent/compose-draft.py').write_bytes(Path(__file__).read_bytes())
record = dict(draft=str(path), bytes=len(text.encode()), lines=len(text.splitlines()),
    sha256=hashlib.sha256(text.encode()).hexdigest(),
    producer_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
    retains_entire_strengthened_resource_packet=True,
    derives_chosen_edge_and_index_from_original_model=True,
    policy='Original permutation selection and full-list projection support; primary needs only chosen-prefix support.',
    quantifiers='Chosen original model precedes outer bounds; retained full primary observer remains universal after its bounds.')
(area / 'parent/draft-v1.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
