exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import difflib
gate = load(HERE / 'root-declaration-gate-v2.json')
assert gate['body_authoring_authorized'] and not gate['compiler_activation_authorized']
old = HERE / 'variants/v2' / (NAME + '.lean')
assert sha(old) == 'abc5f62f9e5bfeeabd6e74df950f2918a854dd264046b5da1fafc27c4d37ec8d'
source = old.read_text()
changes = [
    ('/-- Sequential outcomes retain the node supply on completion or pending return. -/',
     'omit [DecidableEq (EdgeKey Symbol Guard)] in\n/-- Sequential outcomes retain the node supply on completion or pending return. -/'),
    ('    · exact Nat.le_trans reserved (later _ _)',
     '    · exact Nat.le_trans reserved\n        (later (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)\n          {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2})'),
    ('  | empty | var index => exact Nat.le_refl _',
     '  | empty | var index => simp only [build, Outcome.state]; exact Nat.le_refl _'),
    ('          apply bind_mono _ _ next (work_mono (makeEdge symbol constraint values) next)',
     '          apply bind_mono (work (makeEdge symbol constraint values) next) _ next\n            (work_mono (makeEdge symbol constraint values) next)')]
for before, after in changes:
    assert source.count(before) == 1
    source = source.replace(before, after)
for header_file, function in [('public-many.lean.txt','buildMany'),('public-edges.lean.txt','buildEdges')]:
    header = (HERE / 'declaration-plan-v2' / header_file).read_text()[:-1] + ' := by\n'
    before = header + '  cases expression with\n  | nil => exact Nat.le_refl _'
    after = header + '  cases expression with\n  | nil => simp only [' + function + ', Outcome.state]; exact Nat.le_refl _'
    assert source.count(before) == 1
    source = source.replace(before,after)
directory = HERE / 'variants/v3'
directory.mkdir(exist_ok=False)
target = directory / (NAME + '.lean')
target.write_text(source)
assert len(source.splitlines()) <= 180
for file, digest in load(HERE / 'declaration-plan-v2/contracts.json').items():
    path = HERE / 'declaration-plan-v2' / file
    assert sha(path) == digest
    fragment = path.read_text()
    record = next(r for r in load(HERE / 'declaration-plan-v2/insertion-map.json')['compiled_fragments'] if r['file']==file)
    if 'future_body_attachment' in record:
        fragment = fragment[:-1] + record['future_body_attachment']
    assert source.count(fragment) == 1, file
patches = HERE / 'patches'
patches.mkdir()
for earlier,later in [('v1','v2'),('v2','v3')]:
    before = 'variants/' + earlier + '/' + NAME + '.lean'
    after = 'variants/' + later + '/' + NAME + '.lean'
    patch = ''.join(difflib.unified_diff((HERE/before).read_text().splitlines(keepends=True),
        (HERE/after).read_text().splitlines(keepends=True),fromfile=before,tofile=after))
    (patches / (earlier+'-to-'+later+'.patch')).write_text(patch)
save('body-v3-provenance.json',dict(status='SELECTED_NOT_COMPILED',source=str(target.relative_to(HERE)),
    source_sha256=sha(target),source_lines=len(source.splitlines()),previous_source_sha256=sha(old),
    declaration_gate='root-declaration-gate-v2.json',declaration_gate_sha256=sha(HERE/'root-declaration-gate-v2.json'),
    strict1_failure_retained=True,public_types_unchanged=True,new_helpers_or_local_types=False,
    default_declaration_limits=True,all_linters=True,source_hard_stop=180,goal_status='ACTIVE_INCOMPLETE'))
for name in ['write-body-v3.py','strict1-repair-plan.md']:
    with (HERE/name).open('xb') as output:
        output.write(Path('/tmp/mcfta-fresh-node-counter-growth-'+name).read_bytes())
print(json.dumps(load(HERE/'body-v3-provenance.json')))
