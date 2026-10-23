exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import re
owner = Path('/tmp/mcfta-native-node-counter-growth-investigation')
checked_package(owner, '3773a466196bbd1be13f955d183388ba708db2d6b7d2167e0d9af1e3b5271a6e', '41f7e6859edd33acd5150090b309fb63953826fce341a4119b207ec47fab93dd')
index = load(owner / 'source-index.json')
assert [index[k] for k in ['source_count', 'cut_count', 'cut_lines']] == [10, 14, 246]
for source in index['sources']:
    raw = Path(source['path']).read_bytes()
    assert raw == (owner / source['snapshot']).read_bytes() and sha(Path(source['path'])) == source['sha256']
    for cut in source['cuts']:
        assert (owner / cut['snapshot']).read_bytes() == b''.join(raw.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
routes = load(owner / 'import-routes.json')
imports = {}
for source in routes['route_source_identities']:
    assert sha(Path(source['path'])) == source['sha256']
    imports[source['module']] = re.findall(r'^import (\S+)$', Path(source['path']).read_text(), re.M)
    assert imports[source['module']] == source['imports']
for route in routes['public_routes']:
    assert route['route'][0] == route['from'] and route['route'][-1] == route['to']
    assert all(after in imports[before] for before, after in zip(route['route'], route['route'][1:]))
archive(owner, 'native-counter-investigation')
save('root-investigation-review.json', dict(status='ACCEPTED_PUBLIC_API_INVESTIGATION_ONLY',
    root_all_14_public_cuts_246_lines_read=True, root_complete_proposal_and_case_route_read=True,
    root_all_seven_import_routes_and_source_identities_checked=True, full_source_hashes_checked=10,
    same_actual_native_counter_projection=True, all_four_outcomes=True, no_validity_or_success_premise=True,
    no_body_or_compiler_authorized=True, declaration_review_required=True, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted and retained the exact public API investigation; declaration and body gates remain separate.')
