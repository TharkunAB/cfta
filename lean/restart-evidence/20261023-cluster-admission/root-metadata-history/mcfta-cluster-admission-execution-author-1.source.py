exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
assert load(HERE / 'root-execution-declaration-gate.json')['mathematical_body_authoring_authorized']
plan = Path('/tmp/mcfta-cluster-admission-execution-plan')
owner = Path('/tmp/mcfta-cluster-admission-execution-source-v1')
assert not owner.exists()
owner.mkdir()
source = (plan / 'context.lean.txt').read_text() + '''

/-- Compose a yielded prefix with the remaining scan fuel. -/
''' + (plan / 'yielded-header.lean.txt').read_text().rstrip() + ''' := by
  induction used generalizing control before with
  | zero =>
      have same : control = next ∧ before = middle := by
        simpa only [execute, SourceCurrentOriginalRowClusterScan.Outcome.yielded.injEq] using observed
      rcases same with ⟨rfl, rfl⟩
      simp only [Nat.zero_add]
  | succ used ih =>
      cases one : step control before <;>
        simp only [execute, one] at observed
      case yielded following after =>
        simpa only [Nat.succ_add, execute, one] using ih following after observed
      all_goals cases observed

/-- Additional fuel retains the exact completed rows and full state. -/
''' + (plan / 'done-header.lean.txt').read_text().rstrip() + ''' := by
  induction fuel generalizing control before with
  | zero => cases observed
  | succ fuel ih =>
      cases one : step control before <;>
        simp only [execute, one] at observed
      case yielded following middle =>
        simpa only [Nat.succ_add, execute, one] using ih following middle observed
      all_goals simpa only [Nat.succ_add, execute, one] using observed

/-- Two completed scans from the same control and state return the same rows and state. -/
''' + (plan / 'unique-header.lean.txt').read_text().rstrip() + ''' := by
  have firstStable : execute (firstFuel + secondFuel) control before = .done firstRows firstAfter :=
    done_stable firstFuel secondFuel control before firstAfter firstRows first
  have secondStable : execute (secondFuel + firstFuel) control before = .done secondRows secondAfter :=
    done_stable secondFuel firstFuel control before secondAfter secondRows second
  rw [Nat.add_comm secondFuel firstFuel] at secondStable
  exact SourceCurrentOriginalRowClusterScan.Outcome.done.inj (firstStable.symm.trans secondStable)

end MicroCFTA.SourceCurrentOriginalRowClusterExecution
'''
path = owner / (NAME + '.lean')
path.write_text(source)
assert len(source.splitlines()) <= 130
for name, pin in load(plan / 'contracts.json').items():
    fragment = (plan / name).read_text().rstrip()
    if name.endswith('-case.lean.txt'):
        assert source.count(fragment) == 2
    else:
        assert source.count(fragment) == 1
pins = [{'path': path.name, 'bytes': path.stat().st_size, 'sha256': sha(path)}]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_BODY_PENDING_INDEPENDENT_REVIEW', 'source_sha256': sha(path), 'lines': len(source.splitlines()), 'pins_sha256': sha(owner / 'pins.json')}, indent=2) + '\n')
print(json.dumps({'owner': str(owner), 'lines': len(source.splitlines()), 'source_sha256': sha(path), 'pins_sha256': sha(owner / 'pins.json'), 'frozen_sha256': sha(owner / 'FROZEN.json')}))
