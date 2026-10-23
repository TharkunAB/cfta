exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))

owner = Path('/tmp/mcfta-after-demand-counter-investigation')
peer = Path('/tmp/mcfta-after-demand-counter-investigation-review')
checked_package(owner, '96a5f34b70d8f0b25b793c49453d2acc34a690d1655c0c6037361cc000b78a75', 'da7e537e77e7f2c55d4673c0b5f25b4ac39c32c8d849bfd55273910ccab18f43')
checked_package(peer, 'e2cfad0ee7e88d1a859f643f0d6b4c35b91b0cbbdf7f39f38f5df31808ea4d10', '941c360ab5cdaf179093e001dd2bef2eeb5f64e3efb39880fde2a50f8c119122')
assert sha(peer / 'review.json') == '0a4215862b827d4d5e5530f5b265c2c79194d92a3fd0bc2a52c0c92eb28a1fad'
assert load(peer / 'review.json')['status'] == 'CLEAR'
index = load(owner / 'source-index.json')
assert len(index['sources']) == 7
assert sum(len(source['cuts']) for source in index['sources']) == 12
assert sum(cut['end'] - cut['start'] + 1 for source in index['sources'] for cut in source['cuts']) == 417
for source in index['sources']:
    path = Path(source['path'])
    raw = path.read_bytes()
    assert raw == (owner / source['snapshot']).read_bytes() and sha(path) == source['sha256']
    for cut in source['cuts']:
        assert (owner / cut['snapshot']).read_bytes() == b''.join(raw.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
routes = load(owner / 'import-provenance.json')
assert len(routes['route_sources']) == 9
for item in routes['route_sources'].values():
    path = Path(item['path'])
    assert sha(path) == item['sha256']
    assert [line for line in path.read_text().splitlines() if line.startswith('import ')] == item['import_lines']
archive(owner, 'after-demand-counter-investigation')
archive(peer, 'investigation-audit')
save('root-investigation-review.json', dict(status='ACCEPTED_PUBLIC_API_INVESTIGATION_ONLY',
    module=NAME, root_complete_note_assessment_import_routes_and_all_12_cuts_417_lines_read=True,
    root_complete_pair_and_scan_controls_and_H36_source_read_reused_by_exact_live_identity=True,
    full_source_hashes_checked=7, import_route_sources_checked=9,
    same_actual_pair_state_checked_native_heap_counter=True, all_five_outcomes=True,
    no_validity_inputs_readiness_or_success_premise=True,
    public_total_full_pair_state_projection_chosen=True, accessor_requires_no_equality_instances=True,
    public_heads=[['outcomeState', 'def'], ['step_mono', 'theorem'], ['execute_mono', 'theorem']],
    no_existing_pair_or_scan_state_accessor_or_resume=True, no_private_API_required=True,
    source_target=[90,125], whole_source_hard_stop=160, no_padding=True,
    structural_growth_does_not_order_counters=True, no_body_or_compiler_authorized=True,
    exact_declaration_review_required=True, independent_review_sha256=sha(peer / 'review.json'),
    goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the pair API investigation and total-state projection choice. Exact declarations and body review remain required.')
