exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import re

owner = Path('/tmp/mcfta-after-native-counter-investigation')
checked_package(owner, '156b1c852573b1fdfd725f1e2f5bf498f0a85896680941f4f984fa868121f726', '2ce26f44f526f283f847237f932597ec792b9394856ea87a8fd956996c70468a')
index = load(owner / 'source-index.json')
assert len(index['sources']) == 11
assert sum(len(source['cuts']) for source in index['sources']) == 18
assert sum(cut['end'] - cut['start'] + 1 for source in index['sources'] for cut in source['cuts']) == 536
for source in index['sources']:
    raw = Path(source['path']).read_bytes()
    assert raw == (owner / source['snapshot']).read_bytes() and sha(Path(source['path'])) == source['sha256']
    for cut in source['cuts']:
        assert (owner / cut['snapshot']).read_bytes() == b''.join(raw.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
routes = load(owner / 'import-routes.json')
for edge in routes['existing_import_edges']:
    path = ROOT / 'lean/MicroCFTA' / (edge['source'] + '.lean')
    assert sha(path) == edge['source_sha256']
    assert path.read_text().splitlines()[edge['line'] - 1] == 'import MicroCFTA.' + edge['target']
archive(owner, 'after-native-counter-investigation')
save('root-investigation-review.json', dict(status='ACCEPTED_PUBLIC_API_INVESTIGATION_ONLY',
    root_complete_note_import_routes_and_all_18_cuts_536_lines_read=True,
    root_first_four_defining_sources_and_actual_native_Code_read_whole=True,
    full_source_hashes_checked=11, same_actual_checked_demand_counter_projection=True,
    all_five_outcomes=True, no_validity_inputs_fields_or_success_premise=True,
    private_lift_heap_not_public=True, tiny_local_lift_native_projection_permitted=True,
    pair_and_scan_state_accessor_absence_retained=True,
    structural_growth_does_not_order_counters=True,
    no_body_or_compiler_authorized=True, declaration_review_required=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the exact live API investigation. Exact declaration and body reviews remain required.')
