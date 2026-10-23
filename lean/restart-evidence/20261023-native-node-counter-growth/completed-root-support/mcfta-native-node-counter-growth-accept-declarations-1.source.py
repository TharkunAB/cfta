exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import re

owner = Path('/tmp/mcfta-native-node-counter-growth-declaration-plan-v2')
review = Path('/tmp/mcfta-native-node-counter-growth-declaration-audit')
checked_package(owner, 'be2fdbb359ae6fb728f888ee750d576866ef1da3224b40ecc359966699ed7b44', '983c8a5aa9388b4f235a0e0806752d8972e9c69f16998fb32f38e3717d9119e4')
checked_package(review, '268795f52ba813daefe00a41243f3208657c214bc450598c6a662fff00104124', '6192deca78ed68b2ef7b19c653a3181e244ff47b7f90eb8e9a286c206277e3eb')
assert load(review / 'review.json')['status'] == 'CLEAR'
contracts = load(owner / 'contracts.json')
layout = load(owner / 'insertion-map.json')
assert len(contracts) == 6 and sum(len((owner / name).read_bytes().splitlines()) for name in contracts) == 29
assert load(owner / 'declaration-schema.json') == layout['schema']
for (name, digest), entry in zip(contracts.items(), layout['compiled_fragments'], strict=True):
    assert name == entry['file'] and sha(owner / name) == digest == entry['sha256']
    assert (owner / name).read_bytes() == (Path('/tmp/mcfta-native-node-counter-growth-declaration-plan') / name).read_bytes()
index = load(owner / 'source-index.json')
assert [index[key] for key in ['source_count', 'cut_count', 'cut_lines']] == [12, 16, 278]
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
archive(owner, 'declaration-plan')
archive(review, 'declaration-audit')
save('root-declaration-gate.json', dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    module=NAME, public_heads=['step_mono', 'execute_mono', 'resume_mono'], private_helpers=[],
    contracts_sha256=sha(owner / 'contracts.json'), insertion_map_sha256=sha(owner / 'insertion-map.json'),
    root_all_public_and_private_header_types_read=True,
    root_all_schema_layout_owner_attachment_and_body_inventory_metadata_read=True,
    root_all_twelve_scoped_introduced_types_read=True, root_all_six_specialized_equation_types_read=True,
    root_complete_generalized_fuel_IH_three_lines_read=True, restricted_induction_call='ih next after',
    root_all_16_relevant_live_API_cuts_278_lines_read=True, root_all_seven_public_import_routes_checked=True,
    root_whole_context_lines_read=7, root_whole_public_header_lines_read=18,
    root_whole_private_header_lines_read=0, root_whole_local_compiled_fragment_lines_read=4,
    body_haves=2, body_lets=0, body_obtains=0, helpers=0, induction=True,
    recursive_calls=0, termination_by_count=0, whole_source_hard_stop=160,
    whole_source_target=[95, 130], below_target_without_padding_allowed=True,
    default_declaration_limits=True, all_linters=True,
    independent_review_sha256=sha(review / 'review.json'), body_authoring_authorized=True,
    compiler_authorized=False, goal_status='ACTIVE_INCOMPLETE'))

for label, scope, peer, pins, freeze, peer_pins, peer_freeze in [
    ('full', 'full-scope-plan', 'full-plan-audit', 'a12f0a4c984cda5fd325b034f83b3348b78c1ae96ad701289259f35837b963f9', '0ef381e205d156e936fd2aa9adecc9486299a51081d4b6e1895808d91b20d60f', '071b67478ff52e797310ca0fb54d6f9befad87d12eca5467afff6a3ff7f67c0d', '53c39ad4ca3b9bacae4298926577c161802f98031800c6bdf0571e5cc6de5ab5'),
    ('closing', 'closing-scope-plan', 'closing-scope-audit', '7e558e7b849c4e430c2e3229c6acfd6da682d171e156d59b752e9a5a2109ea0f', 'd88adbe2fac521b6f755f52ec73148fba6358f7286d885418069c96442485a6a', '1d9c708f310a09f68177bd837d5715064a0369383f52fe491213a1a1b9bc121e', '0f7400cfed1ceaae5ce31439268762b5001e94055e243081f3988f4e69911842')
]:
    plan = Path('/tmp/mcfta-native-node-counter-growth-' + scope)
    audit = Path('/tmp/mcfta-native-node-counter-growth-' + peer)
    checked_package(plan, pins, freeze)
    checked_package(audit, peer_pins, peer_freeze)
    assert load(audit / 'review.json')['status'] == 'CLEAR'
    bindings = load(plan / 'input-map.json')
    for entry in bindings['basis'].values():
        assert sha(Path(entry['path'])) == entry['sha256']
        assert (plan / entry['snapshot']).read_bytes() == Path(entry['path']).read_bytes()
    for entry in bindings['known_inputs']:
        assert sha(Path(entry['path'])) == entry['sha256']
        if entry['snapshot']:
            assert (plan / entry['snapshot']).read_bytes() == Path(entry['path']).read_bytes()
    archive(plan, scope)
    archive(audit, peer)
    save('root-' + label + '-scope-gate.json', dict(status='ACCEPTED_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
        exact_declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
        scope_plan_sha256=sha(plan / 'plan.md'), independent_review_sha256=sha(audit / 'review.json'),
        root_whole_plan_input_map_crosswalk_and_complete_bases_read=True,
        all_generic_guards_retained=True, future_actual_results_remain_rejecting=True,
        selected_authorship_authorized=True, activation_authorized=False,
        source_target=[209, 215] if label == 'full' else [236, 236],
        source_hard_stop=220 if label == 'full' else 260))
print('Accepted exact declarations and both tooling scopes. Body source and selected tools may now be authored; activation requires separate review.')
