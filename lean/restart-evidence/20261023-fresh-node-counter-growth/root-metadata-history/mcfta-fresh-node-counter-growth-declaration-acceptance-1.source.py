exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-fresh-node-counter-growth-declaration-plan')
review = Path('/tmp/mcfta-fresh-node-counter-growth-declaration-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, '1931d22b0026c6d17fc2e00210ba7c9830b3389138185b00c797bdc0fe132adf', 'b7cf26d3aeeecace96df28d3317df475495912dd84067737471ca4456bf44b50')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'contracts.json') == 'ee6cc72d392e986d2b59174c6cd5dca13ad4377eea1820e91b710213fba49f1a'
contracts = load(owner / 'contracts.json')
assert len(contracts) == 10 and all(isinstance(item, str) for item in contracts.values())
assert sum(len((owner / name).read_bytes().splitlines()) for name in contracts) == 46
assert len(load(owner / 'recursive-call-contracts.json')['calls']) == 7
assert len(load(owner / 'introduced-types.json')['entries']) == 23
assert sha(owner / 'source-index.json') == 'f42a3cbe7d1b9825538be465b1921a043dab3a76c3ff0222afbe3a7f60443e0a'
archive(owner, 'declaration-plan')
archive(review, 'declaration-audit')
save('root-declaration-gate.json', dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY', module=NAME,
    public_heads=['build_mono','buildMany_mono','buildEdges_mono'], private_helpers=['work_mono','bind_mono','request_mono'],
    contracts_sha256=sha(owner / 'contracts.json'), insertion_map_sha256=sha(owner / 'insertion-map.json'),
    independent_review_sha256=expected_review, compiled_fragments=10, compiled_fragment_lines=46,
    root_whole_context_lines_read=9, root_whole_public_header_lines_read=12,
    root_whole_private_header_lines_read=18, root_whole_local_compiled_fragment_lines_read=7,
    root_all_public_and_private_header_types_read=True, root_all_local_have_let_and_lambda_types_read=True,
    root_all_three_recursive_signatures_and_seven_restricted_call_types_read=True,
    root_all_23_scoped_introduced_types_read=True, root_all_13_relevant_live_API_cuts_read=True,
    body_haves=2, body_lets=1, body_obtains=0, helpers=3, recursive_calls=7,
    recursive_mutual_induction=True, tactic_induction=False, termination_by_count=3,
    generalized_environment_and_full_heap=True, callback_pending_bound_derived_not_public_premise=True,
    same_repaired_executor_outcome_state=True, no_public_Dense_Valid_Facts_Good_success_or_counter_oracle=True,
    target_source_lines=[120,155], whole_source_hard_stop=180,
    default_declaration_limits=True, all_linters=True, body_authoring_authorized=True,
    compiler_activation_authorized=False, native_Scan_H23_or_resource_result_claimed=False,
    goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED all exact private/public/local types and restricted mutual recursion contracts. Body authorship only; no compiler activation yet.')
