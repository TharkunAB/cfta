exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-group-admission-proof-verifier-plan')
checked_package(plan,'af2aa2b7b6f49810a6d66318e7d9fbce9497d8b60a5577ef97a715d79593c0bd','5b35ebf0cf6e731d60e90d60784a9780d284de6767d8c2a6a9ae9b62472aba94')
audit = Path('/tmp/mcfta-group-admission-proof-plan-audit')
checked_package(audit,'d39c3080b1fe795840f5cca27b0a85a77c6ecdb7331d5cc19b8282f0608ea4d7','89abd219c1f337dde0bbe08856e230638675762ea33d1839a2e7b119cc7025e5')
assert load(audit / 'review.json')['status'] == 'CLEAR'
archive(plan,'proof-verifier-plan')
archive(audit,'proof-plan-audit')
save('root-proof-verifier-scope-gate.json',dict(status='ACCEPTED_EXACT_SAVED_VERIFIER_SCOPE_BEFORE_AUTHORING',
    module=NAME,public_heads=['groups_admitted'],plan_sha256=sha(plan / 'plan.md'),
    independent_review_sha256=sha(audit / 'review.json'),root_whole_plan_lines_read=40,
    root_complete_H29_V2_basis_code_lines_read=387,root_complete_H29_V2_basis_data_lines_read=1119,
    target_source_lines=[330,380],whole_selected_source_hard_stop=400,
    all_generic_guard_families_required=True,Fin_activation_and_successor_match_raw=True,
    column_view_only_for_local_have_and_obtain=True,
    actual_future_FULL_Audit_TYPE_and_history_fields_must_be_bound=True,
    future_metadata_cut_required=True,selected_source_authoring_accepted=True,
    selected_program_execution_accepted=False,no_checker_framework=True))
print('ACCEPTED source-only saved-verifier scope; final binding waits actual Audit and history records.')
