exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
plan = HERE / 'declaration-plan'
gate = load(HERE / 'root-declaration-gate.json')
assert gate['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
assert gate['body_authoring_authorized'] and not gate['compiler_activation_authorized']
contracts = load(plan / 'contracts.json')
for file, expected in contracts.items():
    assert sha(plan / file) == expected
def raw(file):
    return (plan / file).read_text()
def head(file):
    text = raw(file)
    assert text.endswith('\n')
    return text[:-1] + ' := by\n'
source = raw('context.lean.txt') + '\n'
source += head('private-work.lean.txt') + '''  rw [(SourceCurrentAllocatedFiniteOrdinaryReservations.run_next computation state).1]
  omega

'''
source += head('private-bind.lean.txt') + '''  cases outcome with
  | done value current => exact Nat.le_trans first (later value current)
  | pending key current => exact first

'''
source += head('private-request.lean.txt')
source += head('local-reserved.lean.txt') + '''    rw [SourceCurrentAllocatedFiniteOrdinaryReservations.intern_next]
    omega
  simp only [request]
  split
  · split <;> exact Nat.le_refl _
  · apply bind_mono _ _ state
    · exact Nat.le_trans reserved (later _ _)
    · intro bodyValue afterBody
      exact Nat.le_refl _

mutual
'''
source += head('public-build.lean.txt') + '''  cases expression with
  | empty | var index => exact Nat.le_refl _
  | node edges =>
      simp only [build]
      exact bind_mono _ _ state (buildEdges_mono edges environment state)
        (fun values current => work_mono (makeNode values) current)
  | union members =>
      simp only [build]
      exact bind_mono _ _ state (buildMany_mono members environment state)
        (fun values current => work_mono (makeUnion values) current)
  | binder smart body =>
'''
source += raw('local-callback.lean.txt')
source += head('local-preserved.lean.txt') + '''        intro name current
        exact bind_mono _ _ current (build_mono body (.reference name :: environment) current)
          (fun value afterBody => work_mono (withoutSelfReference name value) afterBody)
      simp only [build]
      apply bind_mono _ _ state (preserved .depth state)
      intro depth afterDepth
      apply bind_mono _ _ afterDepth (preserved (.uninterned (ordinaryLevel depth)) afterDepth)
      intro ordinary afterOrdinary
      exact request_mono smart depth ordinary callback afterOrdinary preserved
termination_by sizeOf expression

'''
source += head('public-many.lean.txt') + '''  cases expression with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      simp only [buildMany]
      apply bind_mono _ _ state (build_mono first environment state)
      intro value next
      apply bind_mono _ _ next (buildMany_mono rest environment next)
      intro values final
      exact Nat.le_refl _
termination_by sizeOf expression

'''
source += head('public-edges.lean.txt') + '''  cases expression with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges]
          apply bind_mono _ _ state (buildMany_mono children environment state)
          intro values next
          apply bind_mono _ _ next (work_mono (makeEdge symbol constraint values) next)
          intro edge afterEdge
          apply bind_mono _ _ afterEdge (buildEdges_mono rest environment afterEdge)
          intro edges final
          exact Nat.le_refl _
termination_by sizeOf expression
end

end MicroCFTA.InternedFreshOrdinaryNodeCounterGrowth
'''
assert len(source.splitlines()) <= gate['whole_source_hard_stop']
assert source.count('  have ') == 2 and source.count('      let callback :') == 1
assert source.count('termination_by sizeOf expression') == 3
variant = HERE / 'variants' / 'v1'
variant.mkdir(parents=True, exist_ok=False)
target = variant / (NAME + '.lean')
with target.open('x') as output:
    output.write(source)
save('body-v1-provenance.json', dict(status='AUTHORED_NOT_COMPILED', source=str(target.relative_to(HERE)),
    source_sha256=sha(target), source_lines=len(source.splitlines()),
    contracts_sha256=sha(plan / 'contracts.json'), declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    root_body_author=True, compiler_activation=False, goal_status='ACTIVE_INCOMPLETE'))
with (HERE / 'body-v1-materializer.py').open('xb') as output:
    output.write(Path('/tmp/mcfta-fresh-node-counter-growth-write-body-v1.py').read_bytes())
print(json.dumps(dict(source=str(target), sha256=sha(target), lines=len(source.splitlines()), compiler_run=False)))
