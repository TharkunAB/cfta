exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-group-admission-closing-tool-plan')
checked_package(plan,'5cfd55938ee861812927081ef0e0fe4140f09b7497fcd7e89d3e6ade4890171f','9cb356fd44edc4b94155ab572c1ec1c8e87f4cb872133ba01fcebd67655d29b8')
audit = Path('/tmp/mcfta-group-admission-closing-plan-audit')
checked_package(audit,'244e047b3eded01801d34c223eaeb62b5e5ac64cedb39e0343d14b49295f8e13','da1f56b3e3c0b218f2dbb0c80c3f5e3512643dd0838d78c198d401e23a2ba30b')
assert load(audit / 'review.json')['status'] == 'CLEAR'
actual = load(HERE / 'actual-proof-cut.json')
assert actual['status'] == 'ACTUAL_AUDIT_AND_HISTORY_BOUND'
assert actual['metrics'] == dict(actual_jobs=3,source_jobs=2,focused_build_jobs=0,audit_jobs=1,failed_jobs=0,warned_source_exit_zero_jobs=0,rejected_public_type_jobs=0)
assert actual['audit']['build_jobs'] == 3649 and actual['audit']['dependencies'] == 75526
archive(plan,'closing-tool-plan')
archive(audit,'closing-plan-audit')
save('root-closing-tool-scope-gate.json',dict(status='ACCEPTED_EXACT_FIVE_TOOL_SCOPE_BEFORE_AUTHORING',
    root_whole_plan_lines_read=28,root_complete_predecessor_lines_read=240,
    independent_review_sha256=sha(audit / 'review.json'),whole_selected_tool_hard_stop=260,
    actual_proof_cut_sha256=sha(HERE / 'actual-proof-cut.json'),actual_metrics=actual['metrics'],actual_audit=actual['audit'],
    baseline_files=110256,older_non_Audit_sources=3647,unchanged_Haskell=298,unchanged_package=207,
    expected_frozen_registries=314,expected_frozen_entries=1410,archive_overrides=5,
    all_guard_families_required=True,mandatory_seal_checkpoint_rerun=True,verify_seal_byte_identity_required=True,
    selected_tool_authoring_accepted=True,selected_tool_execution_accepted=False))
print('ACCEPTED five-tool source adaptation scope with actual Audit and job bindings.')
