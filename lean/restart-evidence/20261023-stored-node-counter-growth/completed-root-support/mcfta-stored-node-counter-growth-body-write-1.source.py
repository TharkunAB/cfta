exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
gate = load(HERE / 'root-declaration-gate.json')
assert gate['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY' and gate['body_authoring_authorized']
plan = HERE / 'declaration-plan'
for name, digest in load(plan / 'contracts.json').items():
    assert sha(plan / name) == digest
def header(name):
    return (plan / name).read_text().rstrip('\n') + ' := by\n'
source = (plan / 'context.lean.txt').read_text() + '\n'
source += header('private-bind.lean.txt') + '''  cases outcome with
  | done value current => exact Nat.le_trans first (later value current)
  | pending key current => exact first

'''
source += header('private-callback.lean.txt') + '''  unfold SourceRecursiveIntersectionMaybeMu.callback
  apply bind_mono _ _ state (InternedFreshOrdinaryNodeCounterGrowth.build_mono _ _ state)
  intro value after
  simp only [work, Outcome.state]
  rw [(SourceCurrentAllocatedFiniteOrdinaryReservations.run_next
    (withoutSelfReference name value) after).1]
  omega

'''
source += header('private-request.lean.txt')
source += header('local-reserved.lean.txt') + '''    rw [SourceCurrentAllocatedFiniteOrdinaryReservations.intern_next]
    omega
  simp only [request]
  split
  · split <;> exact Nat.le_refl _
  · apply bind_mono _ _ state
    · exact Nat.le_trans reserved
        (callback_mono old body (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
          {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2})
    · intro bodyValue afterBody
      exact Nat.le_refl _

'''
source += header('public-execute.lean.txt') + '''  exact InternedFreshOrdinaryNodeCounterGrowth.build_mono _ _ state

'''
source += header('public-unfold.lean.txt') + '''  cases value with
  | mu entry body depth ordinary => exact execute_mono body _ state
  | empty | reference | node | union => exact Nat.le_refl _

'''
source += header('public-maybeMu.lean.txt') + '''  simp only [SourceRecursiveIntersectionMaybeMu.maybeMu]
  split
  · simp only [SourceRecursiveIntersectionMaybeMu.construct]
    apply bind_mono _ _ state (callback_mono _ _ .depth state)
    intro depth afterDepth
    apply bind_mono _ _ afterDepth
      (callback_mono _ _ (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth)
    intro ordinary afterOrdinary
    exact request_mono _ _ depth ordinary afterOrdinary
  · exact Nat.le_refl _

'''
source += 'end MicroCFTA.' + NAME + '\n'
assert len(source.splitlines()) <= gate['whole_source_hard_stop']
target = HERE / 'variants/v1'
target.mkdir(parents=True)
(target / (NAME + '.lean')).write_text(source)
save('body-v1-status.json', dict(status='ROOT_AUTHORED_UNCOMPILED_VARIANT',
    source=str((target / (NAME + '.lean')).relative_to(HERE)),
    source_sha256=sha(target / (NAME + '.lean')), source_lines=len(source.splitlines()),
    declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'), compiler_activation=False))
print((HERE / 'body-v1-status.json').read_text())
