exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import re
import sys

peer_pins, peer_freeze, peer_review = sys.argv[1:]
owner = Path('/tmp/mcfta-demand-node-counter-growth-declaration-plan')
review = Path('/tmp/mcfta-demand-node-counter-growth-declaration-review')
checked_package(owner, '7e2ee292f166548605c4e91e708720623ce9ccffaade82fb138429143ead5191', '7494b1f44ca17d95ff3d7aa42898be0eabf1971ed7b7e0b9ce836e4237c006d7')
checked_package(review, peer_pins, peer_freeze)
assert sha(review / 'review.json') == peer_review and load(review / 'review.json')['status'] == 'CLEAR'
contracts = load(owner / 'contracts.json')
layout = load(owner / 'insertion-map.json')
schema = load(owner / 'declaration-schema.json')
assert len(contracts) == 7 and sum(len((owner / name).read_bytes().splitlines()) for name in contracts) == 34
assert schema == layout['schema']
assert schema['public_heads'] == ['step_mono', 'execute_mono', 'resume_mono']
assert schema['private_helpers'] == ['lift_native'] and schema['introduced_type_entries'] == 10
assert schema['case_equation_specializations'] == 5 and schema['whole_source_hard_stop'] == 160
for (name, digest), entry in zip(contracts.items(), layout['compiled_fragments'], strict=True):
    assert name == entry['file'] and sha(owner / name) == digest == entry['sha256']
    assert len((owner / name).read_bytes().splitlines()) == entry['lines']
index = load(owner / 'source-index.json')
assert len(index['sources']) == 10
assert sum(len(source['cuts']) for source in index['sources']) == 15
assert sum(cut['end'] - cut['start'] + 1 for source in index['sources'] for cut in source['cuts']) == 257
for source in index['sources']:
    raw = Path(source['path']).read_bytes()
    assert raw == (owner / source['snapshot']).read_bytes() and sha(Path(source['path'])) == source['sha256']
    for cut in source['cuts']:
        assert (owner / cut['snapshot']).read_bytes() == b''.join(raw.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
routes = load(owner / 'import-routes.json')
imports = {}
for module, source in routes['route_sources'].items():
    assert sha(Path(source['path'])) == source['sha256']
    lines = re.findall(r'^import (\S+)$', Path(source['path']).read_text(), re.M)
    assert ['import ' + name for name in lines] == source['import_lines']
    imports[module] = lines
assert len(routes['routes']) == 10
for route in routes['routes']:
    assert route['route'][0] in routes['context_imports'] and route['route'][-1] == route['target']
    assert all(after in imports[before] for before, after in zip(route['route'], route['route'][1:]))
archive(owner, 'declaration-plan')
archive(review, 'declaration-audit')
save('root-declaration-gate.json', dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    module=NAME, public_heads=schema['public_heads'], private_helpers=schema['private_helpers'],
    contracts_sha256=sha(owner / 'contracts.json'), insertion_map_sha256=sha(owner / 'insertion-map.json'),
    root_all_public_and_private_header_types_read=True,
    root_all_schema_layout_owner_attachment_and_body_inventory_metadata_read=True,
    root_all_ten_scoped_introduced_types_read=True, root_all_five_specialized_equation_types_read=True,
    root_complete_generalized_fuel_IH_three_lines_read=True, restricted_induction_call='ih next after',
    root_all_15_relevant_live_API_cuts_257_lines_read=True, root_all_ten_public_import_routes_checked=True,
    root_whole_context_lines_read=8, root_whole_public_header_lines_read=17,
    root_whole_private_header_lines_read=4, root_whole_local_compiled_fragment_lines_read=5,
    body_haves=2, body_lets=0, body_obtains=0, helpers=1, induction=True,
    recursive_calls=0, termination_by_count=0, whole_source_hard_stop=160,
    external_native_step_mono_is_not_local_recursion=True,
    whole_source_target=[90, 130], below_target_without_padding_allowed=True,
    default_declaration_limits=True, all_linters=True,
    independent_review_sha256=peer_review, body_authoring_authorized=True,
    compiler_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
investigation = Path('/tmp/mcfta-demand-node-counter-growth-investigation-review')
checked_package(investigation, '29369f176d37113f5fa2e47b2fb55c8344d8b75e8afda1d0e83e8f7b871a70c6', '5ad32e8281d7ceda05bdb59e4aa74f688994a5c22d4d6f0e38e075dd98277439')
assert load(investigation / 'review.json')['status'] == 'SOURCE_ONLY_INVESTIGATION_CLEAR'
archive(investigation, 'investigation-audit')
plan = Path('/tmp/mcfta-demand-node-counter-growth-full-tool-plan')
peer = Path('/tmp/mcfta-demand-node-counter-growth-full-scope-review')
checked_package(plan, '4cc92825288a4fcb4347bf5accd9b91af32c1db48c8328317665240fb5c96379', '8b5b697c203ddad5756bfd9487140d9cf3f3915b4067af4edb40e0b7c94dbc77')
checked_package(peer, 'a8c53cc8746a56abc7aa1f997defd715ab7c72c13c4cf30f31351f97624d2eae', '1ef19cea85e79c270e5cd43d7910881e94cbcbeec9deb4d0b2d8743c8a5ee4a9')
assert load(peer / 'review.json')['status'] == 'SOURCE_ONLY_FULL_TOOL_SCOPE_CLEAR'
bindings = load(plan / 'input-map.json')
for entry in list(bindings['basis'].values()) + bindings['known_inputs']:
    assert sha(Path(entry['path'])) == entry['sha256']
    assert (plan / entry['snapshot']).read_bytes() == Path(entry['path']).read_bytes()
archive(plan, 'full-scope-plan')
archive(peer, 'full-plan-audit')
save('root-full-scope-gate.json', dict(status='ACCEPTED_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    exact_declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    scope_plan_sha256=sha(plan / 'plan.md'), independent_review_sha256=sha(peer / 'review.json'),
    root_whole_plan_input_map_crosswalk_and_complete_bases_read=True,
    all_generic_guards_retained=True, future_actual_results_remain_rejecting=True,
    selected_authorship_authorized=True, activation_authorized=False,
    source_target=[210, 216], source_hard_stop=220))
print('Accepted exact declarations and FULL scope. Root body and selected FULL tools may be authored. Compiler activation requires separate whole-source review.')
