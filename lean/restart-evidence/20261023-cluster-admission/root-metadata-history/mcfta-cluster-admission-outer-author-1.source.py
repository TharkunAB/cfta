exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
assert load(HERE / 'root-outer-declaration-gate.json')['body_authoring_authorized']
plan = HERE / 'outer-declaration-plan-v3'
owner = Path('/tmp/mcfta-cluster-admission-outer-source-v1')
assert not owner.exists()
owner.mkdir()
def fragment(name):
    return (plan / (name + '.lean.txt')).read_text().rstrip('\n')
source = fragment('context') + '\n\n' + fragment('producer-header') + ''' := by
  induction sized : candidates.length using Nat.strongRecOn generalizing candidates keptReversed before with
  | ind size ih =>
      cases candidates with
      | nil =>
          exact ⟨1, keptReversed.reverse, before, rfl, current, admitted⟩
      | cons pivot tail =>
''' + fragment('local-pivotMember') + ''' := by
          exact members pivot List.mem_cons_self
''' + fragment('local-tailMembers') + ''' := by
          intro edge present
          exact members edge (List.mem_cons_of_mem pivot present)
''' + fragment('obtain-boundary') + ''' :=
          SourceCurrentOriginalRowClusterAdmissionBoundary.boundary_complete inventory formulas solver
            bits parent member symbol initialDomains initialValid pivot tail [] keptReversed before
            stable good current semantic allocations idle admitted room pivotMember tailMembers
            (by simp only [List.not_mem_nil, false_implies, implies_true])
''' + fragment('local-smaller') + ''' := by
          simp only [List.length_cons, List.length_nil] at shorter sized
          omega
''' + fragment('obtain-recursive') + ''' :=
          ih next.length smaller next newKept nextMembers middle midStable midGood midAt
            midSemantic midTrace midIdle midAdmission rfl
''' + fragment('local-prefixRun') + ''' := by
          simpa only [SourceCurrentOriginalRowClusterScan.execute,
            SourceCurrentOriginalRowClusterScan.step] using scanned
        refine ⟨used + 1 + fuel, kept, after, ?_, finalAt, finalAdmission⟩
        rw [SourceCurrentOriginalRowClusterExecution.yielded_add (used + 1) fuel _ _ _ _ prefixRun]
        exact done

''' + fragment('adapter-header') + ''' := by
''' + fragment('obtain-producer') + ''' :=
    cluster_complete inventory formulas solver bits parent member symbol initialDomains initialValid
      ((nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))) []
      (fun _ present => present) before stable good current semantic allocations idle admitted room
''' + fragment('obtain-unique') + ''' :=
    SourceCurrentOriginalRowClusterExecution.completed_unique otherFuel fuel
      (.cluster ((nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))) [])
      before otherAfter after otherKept kept otherDone observed
  cases sameState
  exact ⟨otherAt, otherAdmission⟩

end MicroCFTA.SourceCurrentOriginalRowClusterAdmission
'''
path = owner / 'SourceCurrentOriginalRowClusterAdmission.lean'
path.write_text(source)
assert len(source.splitlines()) <= 230
for name in load(plan / 'contracts.json'):
    assert (plan / name).read_text().rstrip('\n') in source, name
pins = [{'path': path.name, 'bytes': path.stat().st_size, 'sha256': sha(path)}]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_BODY_PENDING_INDEPENDENT_REVIEW', 'source_sha256': sha(path), 'lines': len(source.splitlines()), 'pins_sha256': sha(owner / 'pins.json')}, indent=2) + '\n')
print(json.dumps({'lines': len(source.splitlines()), 'source_sha256': sha(path), 'pins_sha256': sha(owner / 'pins.json'), 'frozen_sha256': sha(owner / 'FROZEN.json')}))
