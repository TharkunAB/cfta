exec(compile(open('/tmp/mcfta-scan-node-counter-growth-root-common.py').read(), '/tmp/mcfta-scan-node-counter-growth-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-scan-node-counter-growth-declarations')
peer = Path(sys.argv[1])
checked_package(owner,'ae773a88824b5673ae5267620eb0d26df5cf840a172a574c50069903335fd181','5324df536fc14d2486c375a546de50d7a1347d18d83f9a61a28e4d4d8ffe08fd')
checked_package(peer,sys.argv[2],sys.argv[3])
assert sha(peer / 'review.json') == sys.argv[4] and load(peer / 'review.json')['status'] == 'CLEAR'
contracts = load(owner / 'contracts.json')
assert len(contracts) == 6 and sum(len((owner / name).read_bytes().splitlines()) for name in contracts) == 29
for name,expected in contracts.items():
    assert sha(owner / name) == expected
schema = load(owner / 'declaration-schema.json')
assert schema['public_heads'] == [['outcomeState','def'],['step_mono','theorem'],['execute_mono','theorem']]
assert schema['private_helpers'] == [] and schema['whole_source_hard_stop'] == 140
assert len(load(owner / 'introduced-types.json')['entries']) == 24
families = load(owner / 'case-equations.json')['families']
assert len(families) == 2 and sum(len(family['specialized_types']) for family in families) == 10
assert (owner / 'execute-IH.lean.txt').read_text().rstrip() == load(owner / 'induction-contract.json')['generated_IH_type']
cut_count = cut_lines = 0
for item in load(owner / 'source-index.json')['sources']:
    path = ROOT / item['path']
    raw = path.read_bytes()
    assert raw == (owner / item['snapshot']).read_bytes() and sha(path) == item['sha256']
    for cut in item['cuts']:
        assert (owner / cut['snapshot']).read_bytes() == b''.join(raw.splitlines(keepends=True)[cut['start']-1:cut['end']])
        cut_count += 1
        cut_lines += cut['end']-cut['start']+1
assert (cut_count,cut_lines) == (7,172)
routes = load(owner / 'import-routes.json')
assert len(routes['routes']) == 7 and len(routes['route_sources']) == 38
for item in routes['route_sources'].values():
    assert sha(ROOT / item['path']) == item['sha256'] and (ROOT / item['path']).stat().st_size == item['bytes']
for item in routes['routes']:
    for before,after in zip(item['route'],item['route'][1:]):
        assert 'import '+after in (ROOT / routes['route_sources'][before]['path']).read_text().splitlines()
archive(owner,'declarations')
archive(peer,'declarations-audit')
save('root-declaration-gate.json',dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',module=NAME,
    public_heads=['outcomeState','step_mono','execute_mono'],public_kinds=schema['public_heads'],private_helpers=[],
    contracts_sha256=sha(owner / 'contracts.json'),insertion_map_sha256=sha(owner / 'insertion-map.json'),
    root_all_public_private_local_header_types_and_all_schema_metadata_read=True,
    root_all_24_scoped_introduced_types_read=True,root_all_10_specialized_equation_types_read=True,
    root_all_five_accessor_equations_and_complete_three_line_generalized_fuel_IH_read=True,
    root_all_7_relevant_live_API_cuts_172_lines_read=True,root_all_seven_public_import_routes_checked=True,
    root_context_lines_read=9,root_public_header_lines_read=15,root_local_compiled_fragment_lines_read=5,
    body_haves=2,body_lets=0,body_obtains=0,helpers=0,by_cases=[],induction=True,
    recursive_calls=0,termination_by_count=0,restricted_induction_call='ih next after',
    Pair_and_Scan_done_payload_and_control_types_distinct=True,plain_def_and_by_theorem_attachments_exact=True,
    external_public_H37_step_mono_is_not_local_recursion=True,whole_source_hard_stop=140,
    whole_source_target=[85,115],below_target_without_padding_allowed=True,
    default_declaration_limits=True,all_linters=True,independent_review_sha256=sha(peer / 'review.json'),
    body_authoring_authorized=True,compiler_authorized=False,goal_status='ACTIVE_INCOMPLETE'))
print('Accepted all exact declarations and scoped local types before body authorship. Compilation remains gated.')
