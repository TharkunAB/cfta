exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-stored-node-counter-growth-verifier-scope-plan')
review = Path('/tmp/mcfta-stored-node-counter-growth-verifier-scope-audit')
checked_package(owner, '0040cfc66c9d52e2f9aa63a9571b8fc5a95fd5a91df8d6ce66acbaeb08a890c3', 'e2f2a8348cbfdc6f23182778d72bb9314b03b18992d07bee9b52fafbb02c898b')
checked_package(review, 'e4d8a8dca95f4f112c95889f1688b840d8a056b409f1723a687bca1a0a5bd55b', '5d0422ef922c7068e3d6896c1b37ff2e418025a11ca2cf12c00f428a47fbef15')
assert sha(review / 'review.json') == '6f32cbc908e2f83105ddf89a11870a9c905e4e39b26063be002c30557b607936'
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'verifier-scope-plan')
archive(review, 'verifier-scope-audit')
save('root-proof-verifier-scope-gate.json', dict(status='ACCEPTED_SAVED_VERIFIER_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    root_whole_plan_lines_read=39, root_whole_adaptation_and_future_data_maps_read=True,
    root_all_38_replaced_assertion_scopes_read=True,
    root_whole_402_line_basis_and_528_line_data_prior_reads_reused_with_current_identity=True,
    independent_review_sha256=sha(review / 'review.json'), compiled_fragments=8,
    compiled_fragment_lines=39, context_lines=9, private_header_lines=17, public_header_lines=12,
    local_fragment_lines=1, six_exact_body_inventories=True, scoped_introduced_types=7,
    exact_pattern_binders_and_constructor_only_alternatives_required=True,
    acyclic_unfold_execute_dependency_allowed=True, mutual_self_recursion_and_induction_forbidden=True,
    original_owner_layout_metadata_retained=True, all_generic_guard_families_retained=True,
    target_source_lines=410, whole_selected_source_hard_stop=430,
    future_actual_data_must_remain_rejecting_until_observed=True,
    complete_actual_source_and_history_and_TYPE_and_Audit_reviews_required=True,
    selected_verifier_authoring_authorized=True, selected_execution_authorized=False,
    goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED saved-verifier scope; actual future data remains gated, no selected execution authorized.')
