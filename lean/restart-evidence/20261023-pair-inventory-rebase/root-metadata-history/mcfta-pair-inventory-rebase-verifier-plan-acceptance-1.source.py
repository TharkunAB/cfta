exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-pair-inventory-rebase-proof-verifier-plan')
erratum = Path('/tmp/mcfta-pair-inventory-rebase-proof-verifier-plan-authorship-erratum')
audit = Path('/tmp/mcfta-pair-inventory-rebase-proof-plan-audit')
checked_package(plan, '5e49ccea3775b1089103e4ba81f08ff7737bb7d94ec0b56f67ed845f9e3713ca', '9478221ae95739b980e2d56b905104ad9c11d0df15ce5e35f2255d394345b70c')
checked_package(erratum, '32101ba08f444cd95c13a044a1177a3ca39915f443118a8a9ea135b0bbc00eb9', 'f0d1469ad4ca47fb3b80e72032c2390399d69129eff096aae5652ecfdbd3e4fd')
checked_package(audit, 'c90ec74c2443f93e9d37632182484104accabc38116d7b4ad54a0b028042f540', '3ff206bfea3c2f13949040c2295b5c909b54bce3b02ad1f9a6f437e8a189c2f1')
assert sha(audit / 'review.json') == '65cfad718c919ecfa5077d3204a5f2bbf4640601d318471509820172e0cf1263'
assert load(audit / 'review.json')['status'] == 'CLEAR'
archive(plan, 'proof-verifier-plan')
archive(erratum, 'proof-verifier-plan-authorship-erratum')
archive(audit, 'proof-plan-audit')
save('root-proof-verifier-scope-gate.json', dict(status='ACCEPTED_EXACT_SAVED_VERIFIER_SCOPE_BEFORE_AUTHORING',
    module=NAME, public_heads=['rebase'], plan_sha256=sha(plan / 'plan.md'),
    independent_review_sha256=sha(audit / 'review.json'), root_whole_plan_lines_read=40,
    root_complete_H31_basis_code_lines_read=382, root_complete_H31_basis_data_lines_read=277,
    root_whole_adaptation_map_and_guard_crosswalk_read=True, separate_authorship_erratum_read=True,
    target_source_lines_max=382, whole_selected_source_hard_stop=400,
    all_generic_guard_families_required=True, public_let_occurrences=3, body_let_count=1,
    body_have_count=2, body_obtains=1, obtained_fields=5, induction=False,
    six_fragment_metadata_preserved=True, only_owner_and_path_added_in_data=True,
    actual_future_Audit_TYPE_history_and_final_review_fields_must_be_bound=True,
    both_standalone_modes_at_cwd_slash_required_before_proof_commit=True,
    selected_source_authoring_accepted=True, selected_program_execution_accepted=False,
    no_checker_framework=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED exact H32 saved-verifier scope. Bind all actual facts before final source review.')
