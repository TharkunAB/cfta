exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-rebuild-admission-closing-tool-plan')
audit = Path('/tmp/mcfta-rebuild-admission-closing-plan-audit')
checked_package(plan, '56e6deb3eb57efd8d531d636891626f80dd1a01ae1c89d8eb3b6881a2e35f2f7', 'df7f1dca6d8ed0e8eae21367ba602e0adb677f60da2157023df52d3a9240fc28')
checked_package(audit, 'c76b789746b25360d39c3c3ad8443abe36fb00106ec99101710da459afc74054', 'd699b6672c607965bfb9941a44e282de31b5d70bee55fa40e701a777bd906132')
assert sha(audit / 'review.json') == 'c9556983c837b63bd7fa4abd316de12ba419ce13b7cb8e02bee690e780a2aa69'
assert load(audit / 'review.json')['status'] == 'CLEAR'
cut = load(HERE / 'actual-proof-cut.json')
assert cut['metrics']['actual_jobs'] == 3 and cut['metrics']['failed_jobs'] == 0
assert (cut['audit']['build_jobs'], cut['audit']['dependencies']) == (3650, 75527)
archive(plan, 'closing-tool-plan')
archive(audit, 'closing-plan-audit')
save('root-closing-tool-scope-gate.json', dict(status='ACCEPTED_EXACT_FIVE_TOOL_SCOPE_BEFORE_AUTHORING',
    root_whole_plan_lines_read=24, root_complete_predecessor_lines_read=236,
    independent_review_sha256=sha(audit / 'review.json'), whole_selected_tool_hard_stop=260,
    actual_proof_cut_sha256=sha(HERE / 'actual-proof-cut.json'), actual_metrics=cut['metrics'], actual_audit=cut['audit'],
    baseline_files=111320, older_non_Audit_sources=3648, unchanged_Haskell=298, unchanged_package=207,
    expected_frozen_registries=315, expected_frozen_entries=1411, archive_overrides=5,
    all_guard_families_required=True, mandatory_seal_checkpoint_rerun=True,
    verify_seal_byte_identity_required=True, selected_tool_authoring_accepted=True,
    selected_tool_execution_accepted=False))
print('ACCEPTED exact five-tool source scope with actual Audit and history quantities bound.')
