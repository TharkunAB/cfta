exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-stored-node-counter-growth-declaration-plan')
review = Path('/tmp/mcfta-stored-node-counter-growth-declaration-audit')
checked_package(owner, '847df5dd65b9233859ab6a663aa57eb78ceb065c456910feeee79eb586ad9e29', '423d5a54a0374cb0a046c9d1278db1f77098ae7f14f3243670a31fa7e557ef33')
checked_package(review, '3e2faf56fb9a82b845452ae2d312eaa93081df30aa41dd45d8c0b22f5e9e924e', 'd4f39bb7cf6d0e934001f9af3bdb2932ab5e00fbdf4047b1a7d2feb3fe28a1a8')
assert sha(review / 'review.json') == '52ed9f7c5e58833367bd14ef6649af0b8b590e994a8059efb98f99ebdef6c69f'
assert load(review / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'contracts.json') == '2bf3e6dd8b260c8cd783f6efe5393a07fc447ea7e11a70a6b71431127727ae9b'
layout = load(owner / 'insertion-map.json')
manifest = load(owner / 'contracts.json')
assert len(manifest) == 8 and list(manifest) == [item['file'] for item in layout['compiled_fragments']]
assert sum(item['lines'] for item in layout['compiled_fragments']) == 39
for item in layout['compiled_fragments']:
    assert manifest[item['file']] == item['sha256'] == sha(owner / item['file'])
    assert len((owner / item['file']).read_bytes().splitlines()) == item['lines']
archive(owner, 'declaration-plan')
archive(review, 'declaration-audit')
save('root-declaration-gate.json', dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    module=NAME, public_heads=['execute_mono', 'unfold_mono', 'maybeMu_mono'],
    private_helpers=['bind_mono', 'callback_mono', 'request_mono'], contract_root='declaration-plan',
    contracts_sha256=sha(owner / 'contracts.json'), insertion_map_sha256=sha(owner / 'insertion-map.json'),
    independent_review_sha256=sha(review / 'review.json'), compiled_fragments=8, compiled_fragment_lines=39,
    root_whole_context_lines_read=9, root_whole_private_header_lines_read=17,
    root_whole_public_header_lines_read=12, root_whole_local_compiled_fragment_lines_read=1,
    root_all_public_and_private_header_types_read=True, root_all_seven_scoped_introduced_types_read=True,
    root_all_27_relevant_live_API_cuts_330_lines_read=True, root_all_11_public_import_routes_checked=True,
    root_all_schema_layout_owner_attachment_and_body_inventory_metadata_read=True,
    body_haves=1, body_lets=0, body_obtains=0, helpers=3, induction=False, recursive_calls=0,
    termination_by_count=0, generalized_environment_and_full_heap=True,
    concrete_callback_pending_bound_derived_not_public_premise=True,
    no_public_Dense_Valid_Facts_Good_Available_success_or_counter_oracle=True,
    private_callback_uses_H33_public_build_without_forward_reference=True,
    same_repaired_execute_unfold_maybeMu_outcome_state=True, no_H33_private_helper_import=True,
    global_instance_declaration=False, omit_directives=0, target_source_lines=[95,140],
    whole_source_hard_stop=160, default_declaration_limits=True, all_linters=True,
    body_authoring_authorized=True, compiler_activation_authorized=False,
    native_Scan_H23_or_resource_result_claimed=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED exact declarations, all local types, API routes and independent review; body authoring only.')
