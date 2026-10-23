exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-demand-node-counter-growth-full-preparation')
review = Path('/tmp/mcfta-demand-node-counter-growth-full-tool-audit')
checked_package(owner, '42dca3fcd9abe3ed8541dd6ac2a80921d5a0c373acf9daca78b961dfa8366a4d', '516c6a5caba72f49bb0319e8c92ab2d100d766f7e9eba3cb616994a057999585')
checked_package(review, '7467a3c76c972896a525af2c274aa00291f4df456b74e2390c9d71ba58e60431', 'bd0cd0b143efe92b4a5cd35156ca37b5faf28480e50d4a9d3192fa1447ea6860')
assert sha(review / 'review.json') == '242e221bf091fa82917281c9ba5795ff20ff4fa25c90b78ab8e6a9b93a3b90f9'
assert load(review / 'review.json')['status'] == 'CLEAR'
selected = load(HERE / 'selected-source-gate.json')
assert selected['status'] == 'ACCEPTED_STRICT_SOURCE' and selected['selected_strict'] == 'strict1'
assert (HERE / 'strict1.log').read_bytes() == b'' and load(HERE / 'strict1.json')['exit_code'] == 0
assert sha(HERE / 'strict1.source.lean') == selected['source_sha256']
bindings = load(owner / 'input-map.json')
assert sha(HERE / 'root-declaration-gate.json') == bindings['approved_gate_sha256']
assert sha(HERE / 'root-full-scope-gate.json') == bindings['scope_gate_sha256']
assert sha(HERE / 'declaration-plan/contracts.json') == bindings['contracts_sha256']
assert sha(HERE / 'declaration-plan/insertion-map.json') == bindings['insertion_map_sha256']
scripts = load(owner / 'selected-scripts.json')
assert sum(entry['lines'] for entry in scripts.values()) == 211
assert sum(entry['AST_assertions'] for entry in scripts.values()) == 72
for name, entry in scripts.items():
    path = owner / 'selected' / name
    assert sha(path) == entry['sha256'] and len(path.read_bytes().splitlines()) == entry['lines']
    assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(path.read_text()))) == entry['AST_assertions']
    assert not (HERE / name).exists()
assert not (HERE / (NAME + '.lean')).exists()
archive(owner, 'full-preparation')
archive(review, 'full-tool-audit')
for name in scripts:
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
save('root-full-tool-gate.json', dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE', module=NAME,
    source_sha256=selected['source_sha256'], source_lines=selected['source_lines'], selected_strict='strict1',
    public_heads=selected['public_heads'], private_helpers=['lift_native'],
    independent_review_sha256=sha(review / 'review.json'),
    root_complete_selected_lines_read=211, root_complete_basis_lines_read=210,
    root_all_sources_and_exact_diffs_read=True, selected_lines=211, selected_hard_stop=220,
    diagnostic_tail_lines=20, materializer_cli_arguments=7,
    installed_tools={name: sha(HERE / name) for name in scripts},
    materializer_activation=True, sole_FULL_activation=True, reader_activation_after_actual_FULL=True,
    all_generic_guard_families_preserved=True, canonical_nonoverwrite_guard_retained=True,
    canonical_evidence_source_absent_before_materializer=True, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted and installed reviewed FULL tools for the actual clean strict source.')
