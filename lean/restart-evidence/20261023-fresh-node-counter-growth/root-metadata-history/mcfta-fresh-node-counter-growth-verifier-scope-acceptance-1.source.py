exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-fresh-node-counter-growth-proof-verifier-plan')
review = Path('/tmp/mcfta-fresh-node-counter-growth-proof-verifier-plan-audit')
checked_package(owner, 'c16408c4919375461a43a0f3512cc7e7ae6566909fefa59aaf7490265699d01c', '8a7f6d70709fa8ed7ca67cf4a6556a0c1b726ae607ff94383371c362ade35e14')
checked_package(review, 'fa1ee2519741450dbbdb10d676d61a0d284251c8cd842bb5eb577eaa4cb5a43e', '7bb817f1403e43b7767330eba6fd8fd161d2baef061febe05551d016ce850160')
assert sha(review / 'review.json') == '4e7f2aae825944add7a2e3c9c5e0d2b72228eae4cc3ce2e92fd570ba455ba5c3'
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'proof-verifier-plan')
archive(review, 'proof-verifier-plan-audit')
save('root-proof-verifier-scope-gate.json', dict(status='ACCEPTED_SOURCE_ONLY_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    module=NAME, independent_review_sha256=sha(review / 'review.json'),
    basis_source_lines=384,basis_data_lines=282,basis_AST_assertions=199,
    root_complete_plan_maps_and_all_199_crosswalk_entries_read=True,
    root_complete_basis_previously_reviewed_and_current_identity_checked=True,
    all_six_bodies_and_23_introduced_types_required=True,proper_subexpression_calls=7,
    recursive_signatures_review_only=True,termination_by_count=3,compiled_fragments=10,compiled_fragment_lines=46,
    original_layout_owners_and_metadata_preserved=True,actual_gate_schema_adapter_required=True,
    generic_guards_preserved=True,actual_future_records_rejecting_unbound=True,
    target_source_lines=410,hard_source_stop=430,selected_authorship_authorized=True,
    selected_activation_authorized=False,whole_selected_source_and_actual_evidence_gate_required=True,
    normal_and_live_cwd_slash_before_proof_commit_and_documents=True,goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED reviewed six-body saved-verifier scope. Source authorship only; activation remains gated.')
