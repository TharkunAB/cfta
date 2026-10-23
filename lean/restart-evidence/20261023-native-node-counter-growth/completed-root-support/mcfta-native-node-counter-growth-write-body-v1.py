exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
gate = load(HERE / 'root-declaration-gate.json')
assert gate['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY' and gate['body_authoring_authorized']
assert not gate['compiler_authorized']
contracts = HERE / 'declaration-plan'
def attach(filename):
    return (contracts / filename).read_text().removesuffix('\n') + ' := by\n'
source = (contracts / 'context.lean.txt').read_text() + '\n'
source += attach('public-step.lean.txt')
source += '''  cases code with
  | pure | fail | enter | read | finishNode | finishEdge => exact Nat.le_refl _
  | work job next =>
      simp only [SourceRecursiveIntersectionNative.step,
        SourceRecursiveIntersectionNative.Outcome.state, SourceRecursiveIntersectionThunks.advance]
      rw [(SourceCurrentAllocatedFiniteOrdinaryReservations.run_next job state.machine.heap).1]
      exact Nat.le_add_right _ _
  | optionalBinder key body next =>
'''
source += attach('local-growth.lean.txt')
source += '''        exact InternedFreshOrdinaryStoredNodeCounterGrowth.maybeMu_mono key body state.machine.heap
      cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
      | done value after =>
          simpa only [SourceRecursiveIntersectionNative.step, constructed,
            SourceRecursiveIntersectionNative.Outcome.state, SourceRecursiveIntersectionThunks.advance,
            InternedNestedConstruction.Outcome.state] using growth
      | pending pending after =>
          simpa only [SourceRecursiveIntersectionNative.step, constructed,
            SourceRecursiveIntersectionNative.Outcome.state, SourceRecursiveIntersectionThunks.advance,
            InternedNestedConstruction.Outcome.state] using growth
  | node request next =>
      rw [SourceRecursiveIntersectionNative.node_step_machine]
      exact Nat.le_refl _
  | edge request next =>
      rw [SourceRecursiveIntersectionNative.edge_step_machine]
      exact Nat.le_refl _

'''
source += attach('public-execute.lean.txt')
source += '''  induction fuel generalizing code state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
'''
source += attach('local-first.lean.txt')
source += '''        exact step_mono emptyGuard conjoin code state
      cases observed : SourceRecursiveIntersectionNative.step emptyGuard conjoin code state with
      | yielded next after =>
          simp only [observed, SourceRecursiveIntersectionNative.Outcome.state] at first
          simpa only [SourceRecursiveIntersectionNative.execute, observed] using
            Nat.le_trans first (ih next after)
      | done value after =>
          simpa only [SourceRecursiveIntersectionNative.execute, observed,
            SourceRecursiveIntersectionNative.Outcome.state] using first
      | failed failure after =>
          simpa only [SourceRecursiveIntersectionNative.execute, observed,
            SourceRecursiveIntersectionNative.Outcome.state] using first
      | blocked reason next after =>
          simpa only [SourceRecursiveIntersectionNative.execute, observed,
            SourceRecursiveIntersectionNative.Outcome.state] using first

'''
source += attach('public-resume.lean.txt')
source += '''  cases outcome with
  | yielded code state => exact execute_mono emptyGuard conjoin fuel code state
  | done | failed | blocked => exact Nat.le_refl _

end MicroCFTA.SourceRecursiveIntersectionNativeNodeCounterGrowth
'''
assert len(source.splitlines()) <= 160
for name in load(contracts / 'contracts.json'):
    text = (contracts / name).read_text()
    assert source.count(text if name == 'context.lean.txt' else text.removesuffix('\n') + ' := by\n') == 1
target = HERE / 'variants/v1' / (NAME + '.lean')
target.parent.mkdir(parents=True)
assert not target.exists()
target.write_text(source)
save('body-v1-authorship.json', dict(status='ROOT_BODY_SOURCE_ONLY_AWAITING_INDEPENDENT_REVIEW',
    source=str(target.relative_to(HERE)), sha256=sha(target), lines=len(source.splitlines()),
    compiled_contracts=6, public_heads=gate['public_heads'], private_helpers=[],
    below_soft_target_without_padding=len(source.splitlines()) < 95, no_compiler_run=True))
print(json.dumps(load(HERE / 'body-v1-authorship.json')))
