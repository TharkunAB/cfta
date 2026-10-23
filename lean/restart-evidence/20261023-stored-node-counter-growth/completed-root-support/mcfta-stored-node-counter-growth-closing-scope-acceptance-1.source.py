exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-stored-node-counter-growth-closing-scope-plan')
peer = Path('/tmp/mcfta-stored-node-counter-growth-closing-scope-audit')
checked_package(owner, '7d4f1b7aa57aa9fc886f9ecf95e51a2c7eac4ddec3bcacb6e5360c480e275f27', '70979116ebf77acd1586ad6f6e4795dd8056d1b94d7dad4b072c267938cae3c6')
checked_package(peer, 'df59dda2e0813efd681f16bbb2bbc40812db7b76fb54f9f01dbabd932fc854d4', '5b7832324fec6aeb42929afb7bd7748641aa51a56677fb8f2cd2249d1443b69a')
assert sha(peer / 'review.json') == 'f6dce5d913158c52b74ab406fe3f0b5af8e4ca248f2ae443964f3be093ca608d'
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_plan_or_five_basis_author']
assert sha(owner / 'plan.md') == 'adfbd0f23f7e873becb9d46b8eb87b312fcf8b51791dc3310305098852b074f8'
values = load(owner / 'input-map.json')['known_values']
assert [values[k] for k in ['baseline_files', 'older_non_Audit_Lean', 'Haskell_files', 'active_package_files']] == [116844, 3651, 298, 207]
assert [values[k] for k in ['expected_frozen_registries', 'expected_frozen_entries', 'archived_overrides']] == [318, 1414, 5]
archive(owner, 'closing-scope-plan')
archive(peer, 'closing-scope-audit')
save('root-closing-scope-gate.json', dict(status='ACCEPTED_FIVE_CLOSING_TOOL_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    owner_plan_sha256=sha(owner / 'plan.md'), independent_review_sha256=sha(peer / 'review.json'),
    root_complete_plan_lines_read=28, root_complete_five_basis_lines_read=236, root_complete_input_map_and_crosswalk_read=True,
    basis_AST_assertions=59, selected_target=236, selected_hard_stop=260, all_generic_guards_preserved=True,
    no_new_guard_exception=True, verify_seal_byte_identical=True, mandatory_checkpoint_before_seal=True,
    support_collection_once=True, actual_bindings_required=True, selected_authorship_authorized=True,
    selected_execution_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED closing source scope; selected source authorship only is enabled.')
