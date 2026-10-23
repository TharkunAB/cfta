exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
assert load(HERE / 'root-boundary-declaration-gate.json')['body_authoring_authorized']
plan = HERE / 'boundary-declaration-plan'
owner = Path('/tmp/mcfta-cluster-admission-boundary-source-v1')
assert not owner.exists()
owner.mkdir()
def fragment(name):
    return (plan / (name + '.lean.txt')).read_text().rstrip('\n')
source = fragment('context') + '\n\n' + fragment('public-header') + ''' := by
  dsimp only
''' + fragment('local-parentOriginal') + ''' := by
    exact ⟨parent, inventory.originals parent member, inventory.available parent member,
      (inventory.originals parent member).codec parent⟩
''' + fragment('local-parentAdmitted') + ''' := by
    exact SourceCurrentAllocatedNativeInputInventoryModels.root_valid inventory.source inventory.facts
      holds inventory.roots inventory.originals inventory.available inventory.closed parent member
  revert stable good current semantic allocations idle admitted
  induction remaining generalizing incomparableReversed keptReversed before with
  | nil =>
      intro stable good current semantic allocations idle admitted
        _pivotMember _remainingMembers incomparableMembers
      refine ⟨1, incomparableReversed.reverse, pivot :: keptReversed, before, by omega,
        rfl, ?_, ?_, good, current, semantic, stable, idle, allocations, admitted⟩
      · simp only [List.length_reverse, List.length_nil]
        omega
      · simpa only [List.mem_reverse] using incomparableMembers
  | cons candidate tail ih =>
      intro stable good current semantic allocations idle admitted
        pivotMember remainingMembers incomparableMembers
''' + fragment('local-candidateMember') + ''' := by
        exact remainingMembers candidate List.mem_cons_self
''' + fragment('local-tailMembers') + ''' := by
        intro edge present
        exact remainingMembers edge (List.mem_cons_of_mem candidate present)
''' + fragment('local-symbols') + ''' := by
        exact (of_decide_eq_true (List.mem_filter.mp pivotMember).2).trans
          (of_decide_eq_true (List.mem_filter.mp candidateMember).2).symm
''' + fragment('obtain-comparison') + ''' :=
        SourceCurrentSameSymbolEdgeComparisonCovered.original_rows_complete bits inventory.source
          inventory.facts formulas solver inputs parent parent parentOriginal parentOriginal
          (inventory.available parent member) (inventory.available parent member)
          (inventory.closed parent member) (inventory.closed parent member)
          parentAdmitted parentAdmitted pivot candidate (List.mem_filter.mp pivotMember).1
          (List.mem_filter.mp candidateMember).1 symbols initialDomains initialValid before stable
          good current.contextual semantic current.covered current.growth current.history allocations idle room
''' + fragment('local-known') + ''' := by
        exact ⟨(SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning inventory.source
          inventory.facts holds inputModel parent pivot parentOriginal
          (inventory.available parent member) (inventory.closed parent member) parentAdmitted
          (List.mem_filter.mp pivotMember).1).1,
          (SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning inventory.source
            inventory.facts holds inputModel parent candidate parentOriginal
            (inventory.available parent member) (inventory.closed parent member) parentAdmitted
            (List.mem_filter.mp candidateMember).1).1⟩
''' + fragment('local-middleAt') + ''' := by
        exact ⟨midContextual, midCovered, grows_trans current.growth extension.heap,
          extends_trans current.history extension.history⟩
''' + fragment('local-middleAdmission') + ''' := by
        exact (SourceCurrentSameSymbolEdgeRequestAdmission.completed_admitted inputView inputModel
          inputRanked holds pivot candidate common before middle fuel stable admitted known done).2
''' + fragment('obtain-prefix') + ''' :=
        SourceCurrentOriginalRowClusterScan.comparison_lift fuel pivot candidate common tail
          incomparableReversed keptReversed (.call (pivot, candidate) []) before middle done
''' + fragment('local-prefixRun') + ''' := by
        simpa only [SourceCurrentOriginalRowClusterScan.execute,
          SourceCurrentOriginalRowClusterScan.step] using resumed
''' + fragment('case-promoted') + '''
      · rcases promoted with ⟨notDropped, promoted⟩
        refine ⟨used + 1, candidate :: (incomparableReversed.reverse ++ tail), keptReversed,
          middle, by omega, ?_, ?_, ?_, midGood, middleAt, midSemantic, midStable,
          midIdle, midTrace, middleAdmission⟩
        · simpa only [ite_eq_right notDropped, ite_eq_left promoted] using prefixRun
        · simp only [List.length_cons, List.length_append, List.length_reverse]
          omega
        · intro edge present
          rcases List.mem_cons.mp present with rfl | present
          · exact candidateMember
          · rcases List.mem_append.mp present with present | present
            · exact incomparableMembers edge (List.mem_reverse.mp present)
            · exact tailMembers edge present
      · ''' + fragment('local-nextIncomparable').lstrip() + '''
''' + fragment('local-nextMembers') + ''' := by
          dsimp only [nextIncomparable]
          split
          · exact incomparableMembers
          · intro edge present
            rcases List.mem_cons.mp present with rfl | present
            · exact candidateMember
            · exact incomparableMembers edge present
''' + fragment('local-nextLength') + ''' := by
          dsimp only [nextIncomparable]
          split
          · omega
          · simp only [List.length_cons]
            omega
''' + fragment('local-resumedScan') + ''' := by
''' + fragment('case-dropped') + '''
          · simpa only [dropped, ↓reduceIte, nextIncomparable] using prefixRun
          · ''' + fragment('local-notPromoted').lstrip() + ''' := by
              exact fun equal => promoted ⟨dropped, equal⟩
            simpa only [dropped, notPromoted, ↓reduceIte, nextIncomparable] using prefixRun
''' + fragment('obtain-recursive') + ''' :=
          ih (incomparableReversed := nextIncomparable) (keptReversed := keptReversed)
            (before := middle) midStable midGood middleAt midSemantic midTrace midIdle
            middleAdmission pivotMember tailMembers nextMembers
        refine ⟨used + 1 + more, next, newKept, after, by omega, ?_, ?_, nextMembers,
          afterGood, afterAt, afterSemantic, afterStable, afterIdle, afterTrace, afterAdmission⟩
        · rw [SourceCurrentOriginalRowClusterExecution.yielded_add (used + 1) more
            _ _ _ _ resumedScan]
          exact scanned
        · simp only [List.length_cons]
          omega

end MicroCFTA.SourceCurrentOriginalRowClusterAdmissionBoundary
'''
path = owner / 'SourceCurrentOriginalRowClusterAdmissionBoundary.lean'
path.write_text(source)
assert len(source.splitlines()) <= 230
for name, digest in load(plan / 'contracts.json').items():
    text = (plan / name).read_text().rstrip('\n')
    if name in ['local-nextIncomparable.lean.txt', 'local-notPromoted.lean.txt']:
        assert text.lstrip() in source
    else:
        assert text in source, name
pins = [{'path': path.name, 'bytes': path.stat().st_size, 'sha256': sha(path)}]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_BODY_PENDING_INDEPENDENT_REVIEW', 'source_sha256': sha(path), 'lines': len(source.splitlines()), 'pins_sha256': sha(owner / 'pins.json')}, indent=2) + '\n')
print(json.dumps({'owner': str(owner), 'lines': len(source.splitlines()), 'source_sha256': sha(path), 'pins_sha256': sha(owner / 'pins.json'), 'frozen_sha256': sha(owner / 'FROZEN.json')}))
