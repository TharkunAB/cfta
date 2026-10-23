exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
gate = load(HERE / 'root-declaration-gate.json')
assert gate['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY' and gate['body_authoring_authorized']
assert not gate['compiler_authorized']
contracts = HERE / 'declaration-plan'

def attach(filename):
    return (contracts / filename).read_text().removesuffix('\n') + ' := by\n'

source = (contracts / 'context.lean.txt').read_text() + '\n'
source += attach('private-lift.lean.txt')
source += '''  cases outcome <;> rfl

'''
source += attach('public-step.lean.txt')
source += '''  cases control with
  | code code =>
'''
source += attach('local-nativeGrowth.lean.txt')
source += '''        exact SourceRecursiveIntersectionNativeNodeCounterGrowth.step_mono
          SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin code state.native
      cases code with
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          simpa only [SourceRecursiveIntersectionNative.edge_step_machine] using nativeGrowth
      | pure | fail | work | enter | read | optionalBinder | node | finishNode | finishEdge =>
          simpa only [SourceEqualityNativeDemand.step, lift_native] using nativeGrowth
  | edgeBody request next =>
      change state.native.machine.heap.nodes.next ≤
        (SourceEqualityNativeDemand.body request next state).state.native.machine.heap.nodes.next
      rw [SourceEqualityNativeDemandOperations.body_native]
      exact Nat.le_refl _

'''
source += attach('public-execute.lean.txt')
source += '''  induction fuel generalizing control state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
'''
source += attach('local-first.lean.txt')
source += '''        exact step_mono control state
      cases observed : SourceEqualityNativeDemand.step control state with
      | yielded next after =>
          simp only [observed, SourceEqualityNativeDemand.Outcome.state] at first
          simpa only [SourceEqualityNativeDemand.execute, observed] using
            Nat.le_trans first (ih next after)
      | done value after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first
      | failed failure after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first
      | constraintError message after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first
      | blocked reason next after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first

'''
source += attach('public-resume.lean.txt')
source += '''  cases outcome with
  | yielded next after => exact execute_mono fuel next after
  | done | failed | constraintError | blocked => exact Nat.le_refl _

end MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth
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
    compiled_contracts=7, public_heads=gate['public_heads'], private_helpers=['lift_native'],
    below_soft_target_without_padding=len(source.splitlines()) < 90, no_compiler_run=True))
print(json.dumps(load(HERE / 'body-v1-authorship.json')))
