exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
owner = Path('/tmp/mcfta-native-node-counter-growth-full-preparation-source')
review = Path('/tmp/mcfta-native-node-counter-growth-full-tool-audit')
checked_package(owner, 'd3bff77ef6146ef48c1be9818f9e8a8c47b7d2982efa873092f652abbb2bf3ba', '7a36501a00251b7d7fafd19465759d82a24c4ecfc00cf59aca6f6a7e0157739b')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review and load(review / 'review.json')['status'] == 'CLEAR'
selected = load(HERE / 'selected-source-gate.json')
assert selected['status'] == 'ACCEPTED_STRICT_SOURCE' and selected['selected_strict'] == 'strict1'
assert (HERE / 'strict1.log').read_bytes() == b'' and load(HERE / 'strict1.json')['exit_code'] == 0
assert sha(HERE / 'strict1.source.lean') == selected['source_sha256']
bindings = load(owner / 'input-map.json')
for entry in bindings['actual_gate_refs'].values():
    assert sha(Path(entry['path'])) == entry['sha256']
scripts = load(owner / 'selected-scripts.json')
assert sum(entry['lines'] for entry in scripts.values()) == 210
assert sum(entry['AST_assertions'] for entry in scripts.values()) == 71
for name, entry in scripts.items():
    assert sha(owner / 'selected' / name) == entry['sha256']
    assert len((owner / 'selected' / name).read_bytes().splitlines()) == entry['lines']
    assert not (HERE / name).exists()
assert not (HERE / (NAME + '.lean')).exists()
archive(owner, 'full-preparation')
archive(review, 'full-tool-audit')
for name in scripts:
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
save('root-full-tool-gate.json', dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE', module=NAME,
    source_sha256=selected['source_sha256'], source_lines=selected['source_lines'], selected_strict='strict1',
    public_heads=selected['public_heads'], private_helpers=[], independent_review_sha256=expected_review,
    root_complete_selected_lines_read=210, root_complete_basis_lines_read=209,
    root_all_sources_and_exact_diffs_read=True, selected_lines=210, selected_hard_stop=220,
    diagnostic_tail_lines=20, materializer_cli_arguments=7,
    installed_tools={name: sha(HERE / name) for name in scripts},
    materializer_activation=True, sole_FULL_activation=True, reader_activation_after_actual_FULL=True,
    all_generic_guard_families_preserved=True, canonical_nonoverwrite_guard_retained=True,
    canonical_evidence_source_absent_before_materializer=True, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted and installed the complete reviewed FULL tools for the clean strict source.')
