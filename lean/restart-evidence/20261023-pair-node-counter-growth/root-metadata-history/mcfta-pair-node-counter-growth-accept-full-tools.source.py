exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-pair-node-counter-growth-full-preparation')
peer = Path('/tmp/mcfta-pair-node-counter-growth-full-tool-audit')
checked_package(owner, '4fb96a30fb77de8b974ec3c9f706d0e532b1a134e2a549c24c2c5961ad7497d7', 'bb4f038602281d9fbc72c6efff07b1a223d85f5d35bae511a3eaa9a6ffd8126c')
checked_package(peer, '90b9eb3fb3cb5d802ed7cecd758a669981ca55eeafaf9435d41426cd87a7a5e6', 'bf0b26de760df0b24b0570e0915a51d21316ce2a6f2f108d4423eb7748007633')
assert sha(peer / 'review.json') == '9c4089d0f7d4491647eb644f2dc58539b07ccf3e929fafac0d4199dbb0833a43'
assert load(peer / 'review.json')['status'] == 'CLEAR'
pins = load(owner / 'selected-scripts.json')
assert set(pins) == {'prepare-full.py','check-full-public.py'}
assert sum(pin['lines'] for pin in pins.values()) == 213 <= 235
assert sum(pin['assertions'] for pin in pins.values()) == 73
for name, pin in pins.items():
    source = owner / 'selected' / name
    assert sha(source) == pin['sha256'] and source.stat().st_size == pin['bytes']
    assert len(source.read_bytes().splitlines()) == pin['lines']
    assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(source.read_text()))) == pin['assertions']
    assert not (HERE / name).exists()
assert load(HERE / 'selected-source-gate.json')['source_sha256'] == '6cfaf5e340d26b8c838f51d93fb3ae0e03b098510ca41b5021ada4e96b72c2e8'
assert load(HERE / 'root-full-scope-gate.json')['selected_hard_stop'] == 235
archive(owner, 'full-preparation')
archive(peer, 'full-preparation-audit')
for name in pins:
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
save('root-full-tool-gate.json', dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    module=NAME, source_sha256=load(HERE / 'selected-source-gate.json')['source_sha256'], source_lines=96,
    selected_strict='root-pair-node-counter-growth-strict-1',
    public_heads=['outcomeState','step_mono','execute_mono'], private_helpers=[],
    independent_review_sha256=sha(peer / 'review.json'), root_complete_selected_lines_read=213,
    root_complete_basis_lines_read=211, root_all_sources_and_exact_diffs_read=True,
    selected_lines=213, selected_hard_stop=235, selected_assertions=73,
    diagnostic_tail_lines=20, materializer_cli_arguments=7,
    installed_tools={name:sha(HERE / name) for name in pins}, materializer_activation=True,
    sole_FULL_activation=True, reader_activation_after_actual_FULL=True,
    all_generic_guard_families_preserved=True, canonical_nonoverwrite_guard_retained=True,
    canonical_evidence_source_absent_before_materializer=True, goal_status='ACTIVE_INCOMPLETE'))
print('Activated the exact reviewed FULL materializer and reader for the selected strict source.')
