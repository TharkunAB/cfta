exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-pair-inventory-rebase-closing-tool-plan')
audit = Path('/tmp/mcfta-pair-inventory-rebase-closing-plan-audit')
checked_package(plan, 'f754b3b0f48657bfe7630e07df722cb6b11b7f4fe02383b009a64399212721ef', '1266f2c0d25d8567497be8ebc19825069ba2b893b1330dddc4526c2c8f3acb30')
checked_package(audit, '07da7c4864cf3049e341650e1fb20ed765f8c3d037d3007d16b6bc6d42de7871', '6ec2bee5459d0111cfebe58ef75ce76c95a931c0f7b1ac87f6ceb96650c3f019')
assert sha(audit / 'review.json') == 'ca4c32a396a5ed26781a2648ad623039b799e31e4d1ab25a72e4e90aacbe8108'
assert load(audit / 'review.json')['status'] == 'CLEAR'
actual = load(HERE / 'actual-proof-cut.json')
assert actual['audit']['build_jobs'] == 3651 and actual['audit']['dependencies'] == 75528
assert actual['audit']['log_sha256'] == sha(HERE / 'audit1.log')
archive(plan, 'closing-tool-plan')
archive(audit, 'closing-plan-audit')
save('root-closing-tool-scope-gate.json', dict(status='ACCEPTED_EXACT_FIVE_CLOSING_TOOL_SCOPE_BEFORE_AUTHORING',
    module=NAME, plan_sha256=sha(plan / 'plan.md'), independent_review_sha256=sha(audit / 'review.json'),
    root_whole_plan_lines_read=28, root_complete_H31_basis_lines_read=236,
    root_whole_input_map_guard_crosswalk_and_references_read=True,
    target_source_lines=236, whole_selected_source_hard_stop=260,
    baseline_files=112408, older_Lean_sources=3649, Haskell_files=298, active_package_files=207,
    frozen_registries=316, frozen_entries=1412, archive_overrides=5,
    actual_proof_cut_sha256=sha(HERE / 'actual-proof-cut.json'), actual_Audit=actual['audit'],
    all_generic_guards_retained=True, verify_seal_must_remain_byte_identical=True,
    both_saved_modes_before_proof_commit=True, mandatory_checkpoint_rerun_before_seal_writes=True,
    support_collection_exactly_once=True, selected_source_authoring_accepted=True,
    selected_program_execution_accepted=False, network_commands_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED exact five-closing-tool scope with actual Audit and history bound.')
