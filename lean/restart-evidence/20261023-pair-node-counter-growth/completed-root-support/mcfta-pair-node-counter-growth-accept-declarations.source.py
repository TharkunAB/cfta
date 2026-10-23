exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))

owner = Path('/tmp/mcfta-pair-node-counter-growth-declaration-plan-v2')
peer = Path('/tmp/mcfta-pair-node-counter-growth-declaration-review-v2')
scope = Path('/tmp/mcfta-pair-node-counter-growth-full-tool-plan')
scope_peer = Path('/tmp/mcfta-pair-node-counter-growth-full-scope-audit')
checked_package(owner, '331a395d4dbe66a14553ad7ef046b8ff260f75715301e01640e3aa017d0af56a', 'dcf6473f1ec3d248435cb7ea3bb7e2e24b59f6173a45f379c39821c4bdef831c')
checked_package(peer, 'fe9ba10f40056fa5d2a2fbbbb531a643ee978756bde033927c5ca8ef0eaf7de6', '6fd4063a63811b6b051a75ec05d282abc3f81115199cca642b6bc85a88deb7d3')
checked_package(scope, '10adc878358aac5f6ba99ee78f302c0a26fa3191b767a72a1951b18e15ac2263', '02b60c161d29d88e2a0823846d7c4d57af40fb73ea7bbeca95b3a77152adbca7')
checked_package(scope_peer, 'd83a35954ac431a8318128eaccbcfbddb5bc45ca4ca3121f0b4fab6187fa0d1d', '45901d7e5a5412e5853ee85349edb0203cd22cc5b8a2834557fa5f23f51b89c6')
assert sha(peer / 'review.json') == 'd5ecc6ab2ed830228747a55320189ce31d08b87d8b0dafe91b8049d37ad958c6'
assert load(peer / 'review.json')['status'] == 'CLEAR'
assert sha(scope_peer / 'review.json') == 'eb7089a7e81934a09e351c91b62841274c4ee0627452cf5fc5592a9d9a64835b'
assert load(scope_peer / 'review.json')['status'] == 'CLEAR'
contracts = load(owner / 'contracts.json')
layout = load(owner / 'insertion-map.json')
schema = load(owner / 'declaration-schema.json')
assert list(contracts) == schema['compiled_contract_order']
assert len(contracts) == 7 and schema['compiled_contract_lines'] == 29
for (filename, digest), record in zip(contracts.items(), layout['compiled_fragments'], strict=True):
    assert filename == record['file'] and sha(owner / filename) == digest == record['sha256']
    assert len((owner / filename).read_bytes().splitlines()) == record['lines']
assert sum(record['lines'] for record in layout['compiled_fragments']) == 29
assert schema['public_heads'] == [['outcomeState', 'def'], ['step_mono', 'theorem'], ['execute_mono', 'theorem']]
assert schema['private_helpers'] == [] and schema['new_definitions'] == ['outcomeState']
assert schema['introduced_type_entries'] == 28 and schema['case_equation_specializations'] == 14
assert schema['restricted_induction_call_terms'] == ['ih next after']
original = owner / 'original-v1'
for item in original.rglob('*'):
    if item.is_file() and item.name not in {'pins.json', 'FROZEN.json'} and item.relative_to(original).as_posix() != 'case-equations.json':
        assert item.read_bytes() == (owner / item.relative_to(original)).read_bytes()
before = load(original / 'case-equations.json')
after = load(owner / 'case-equations.json')
before['families'][0]['actual_type'] = after['families'][0]['actual_type']
assert before == after
assert after['families'][0]['actual_type'].endswith('(InternedConstructorTemplates.EdgeValue Symbol Guard)')
index = load(owner / 'source-index.json')
assert len(index['sources']) == 5
assert sum(len(source['cuts']) for source in index['sources']) == 11
assert sum(cut['end'] - cut['start'] + 1 for source in index['sources'] for cut in source['cuts']) == 241
for source in index['sources']:
    path = Path(source['path'])
    raw = path.read_bytes()
    assert raw == (owner / source['snapshot']).read_bytes() and sha(path) == source['sha256']
    for cut in source['cuts']:
        assert (owner / cut['snapshot']).read_bytes() == b''.join(raw.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
routes = load(owner / 'import-routes.json')
assert len(routes['routes']) == 7 and len(routes['route_sources']) == 39
for item in routes['route_sources'].values():
    path = Path(item['path'])
    assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes']
    assert [line for line in path.read_text().splitlines() if line.startswith('import ')] == item['import_lines']
for route in routes['routes']:
    for left, right in zip(route['route'], route['route'][1:]):
        assert 'import ' + right in routes['route_sources'][left]['import_lines']
assert git('rev-parse', 'HEAD').strip() == START
archive(owner, 'declaration-plan')
archive(peer, 'declaration-audit')
archive(scope, 'full-scope-plan')
archive(scope_peer, 'full-scope-audit')
save('root-declaration-gate.json', dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    module=NAME, public_heads=[pair[0] for pair in schema['public_heads']],
    public_kinds=schema['public_heads'], private_helpers=[],
    contracts_sha256=sha(owner / 'contracts.json'), insertion_map_sha256=sha(owner / 'insertion-map.json'),
    root_all_public_and_private_header_types_read=True,
    root_all_schema_layout_owner_attachment_and_body_inventory_metadata_read=True,
    root_all_28_scoped_introduced_types_read=True, root_all_14_specialized_equation_types_read=True,
    root_all_five_accessor_equations_read=True, root_complete_generalized_fuel_IH_three_lines_read=True,
    restricted_induction_call='ih next after', root_all_11_relevant_live_API_cuts_241_lines_read=True,
    root_all_seven_public_import_routes_checked=True, root_whole_context_lines_read=9,
    root_whole_public_header_lines_read=15, root_whole_private_header_lines_read=0,
    root_whole_local_compiled_fragment_lines_read=5, body_haves=2, body_lets=0, body_obtains=0,
    helpers=0, by_cases=['reversed'], induction=True, recursive_calls=0, termination_by_count=0,
    whole_source_hard_stop=160, external_checked_step_mono_is_not_local_recursion=True,
    whole_source_target=[90,125], below_target_without_padding_allowed=True,
    default_declaration_limits=True, all_linters=True,
    independent_review_sha256=sha(peer / 'review.json'),
    exact_metadata_type_correction_retains_complete_V1=True,
    body_authoring_authorized=True, compiler_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
save('root-full-scope-gate.json', dict(status='ACCEPTED_SOURCE_ONLY_FULL_TOOL_SCOPE',
    module=NAME, whole_bases_read=211, baseline_assertions=72, selected_target=[211,220],
    selected_hard_stop=235, explicit_literal_per_header_attachments=True,
    definition_attachment=' :=\n', theorem_attachment=' := by\n',
    all_generic_guards_retained=True, parser_relaxation_authorized=False,
    selected_authoring_authorized=True, selected_activation_authorized=False,
    actual_results_unbound=True, independent_review_sha256=sha(scope_peer / 'review.json')))
print('Accepted exact H37 declarations and FULL source scope. Body and selected tool authoring may proceed; execution remains gated.')
