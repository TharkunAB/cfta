exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-fresh-node-counter-growth-closing-tool-plan')
review = Path('/tmp/mcfta-fresh-node-counter-growth-closing-plan-audit')
checked_package(owner, '0e6be090a19fffe06bde8ce63e070755e575e5d4f03eacbd8a6d210423181489', 'dfb0539f28946279c75efe1415f2192ca825072c80270a6563b128929cd2baae')
checked_package(review, '810e3671710423f80dd96fafc970a49252d6c98506d7f475ac0aae042674b636', '6b67f81ea0e4b0b81f025540d48bf750ae16e2f6a7b8175b8b3cf28476e7b4b0')
assert sha(review / 'review.json') == '75570c094177815041ba4d91b8d860e3f5b05e5704988e219a44de103f08841f'
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'closing-tool-plan')
archive(review, 'closing-plan-audit')
assessment = Path('/tmp/mcfta-next-node-counter-lift-assessment')
checked_package(assessment, '76bd4bbc60bde41327e561236febc04c232a285b265a20fb407a4fb519a01106', 'a14ac602b0e7baad9c602fedb6d17a36a4f525d268bef159d9cc083254a9404d')
archive(assessment, 'next-counter-lift-assessment')
save('root-closing-tool-scope-gate.json', dict(status='ACCEPTED_SOURCE_ONLY_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    module=NAME,independent_review_sha256=sha(review / 'review.json'),
    root_complete_plan_map_crosswalk_and_236_basis_lines_read=True,basis_AST_assertions=59,
    selected_target=236,selected_hard_stop=260,verify_seal_byte_identical=True,
    baseline_files=113643,older_non_audit_Lean=3650,Haskell_files=298,active_package_files=207,
    frozen_registries=317,frozen_entries=1413,archive_overrides=5,
    generic_guards_preserved=True,nine_LF_inverses_and_FINDINGS_first=True,
    nested_component_control_hashes_required=True,normal_and_live_cwd_slash_required=True,
    support_once=True,checkpoint_rerun_before_seal_writes=True,no_network_in_five=True,
    actual_Audit_required_before_binding=True,actual_future_records_rejecting_unbound=True,
    selected_authorship_authorized_after_actual_Audit=True,selected_activation_authorized=False,
    next_counter_lift_assessment_scope='SOURCE_ONLY_NOT_A_PROOF',root_complete_28_line_next_note_read=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED reviewed five-tool scope; binding waits for actual Audit. Archived the source-only next-lift assessment.')
