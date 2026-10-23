exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-rebuild-admission-proof-verifier-plan')
audit = Path('/tmp/mcfta-rebuild-admission-proof-plan-audit')
checked_package(plan, 'f5e42d20c26d848cc411d4c62426453427468dffa0a95d9ecb20c566f2d0d521', '572e7e4b4560728862b5141e34339e51d83ed8475be49733795c591986793173')
checked_package(audit, '0cc391805f1fede38b4de6c519fbe1baafdbc2e8ab8163fccfacb1d4e682cea4', '645664a0d9e8bacfe564b532fe36b94d0b125a8642d3d18ddac14194a5fe0a63')
assert sha(audit / 'review.json') == '99bc05f09ebe482929315e43af4cfd9414e37eb95cde32572df6aad0a13d0306'
assert load(audit / 'review.json')['status'] == 'CLEAR'
archive(plan, 'proof-verifier-plan')
archive(audit, 'proof-plan-audit')
save('root-proof-verifier-scope-gate.json', dict(status='ACCEPTED_EXACT_SAVED_VERIFIER_SCOPE_BEFORE_AUTHORING',
    module=NAME, public_heads=['rebuilt_admitted'], plan_sha256=sha(plan / 'plan.md'),
    independent_review_sha256=sha(audit / 'review.json'), root_whole_plan_lines_read=40,
    root_complete_H30_basis_code_lines_read=383, root_complete_H30_basis_data_lines_read=331,
    root_whole_adaptation_map_guard_crosswalk_and_proposed_review_schemas_read=True,
    target_source_lines_max=383, whole_selected_source_hard_stop=400,
    all_generic_guard_families_required=True, public_let_count=4, body_let_count=0,
    body_have_count=0, body_obtains=1, introduced_arrow_fields=3, induction=False,
    only_H30_specific_alias_receipt_removed=True,
    actual_future_Audit_TYPE_history_and_final_review_fields_must_be_bound=True,
    both_standalone_modes_at_cwd_slash_required_before_proof_commit=True,
    selected_source_authoring_accepted=True, selected_program_execution_accepted=False,
    no_checker_framework=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED exact saved-verifier source scope; final binding waits actual Audit, TYPE reviews and history.')
