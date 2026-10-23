exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import ast
import sys
owner = Path('/tmp/mcfta-fresh-node-counter-growth-proof-verifier-source')
review = Path('/tmp/mcfta-fresh-node-counter-growth-proof-verifier-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, 'f411d21dc5f270e9313ce7bdd6c025a53e83389e4b92696da1c8d5c8a6b59d34', '1e69e207d0ac65858d26e4fb88eab37782f85aeedd2343e12a739ef8a6e4afcc')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
code = (owner / 'verify-proofs.py').read_bytes()
assert len(code.splitlines()) == 402
assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(code))) == 212
assert len((owner / 'bound-data.json').read_bytes().splitlines()) == 528
assert sha(HERE / 'source-history-gate.json') == 'e57b389eea481bc2fc1465b45bf3bf6d65c60cf64ac976ba3c0fac74ff84183d'
archive(owner, 'proof-verifier-preparation')
archive(review, 'proof-verifier-audit')
for name, expected in [('verify-proofs.py', 'e3a7dbe25344315aba725cc63b502fd5efe6e2fba78ef50d53d5e96bc8479716'),
        ('bound-data.json', '511742ee2076a23736fd42427ee6081c9548848ca305c65b5bfa448036a8eb73')]:
    assert not (HERE / name).exists() and sha(owner / name) == expected
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'), bound_data_sha256=sha(HERE / 'bound-data.json'),
    root_whole_selected_code_lines_read=402, root_whole_actual_bound_data_lines_read=528,
    root_whole_basis_previously_reviewed=True, root_whole_adaptation_diff_read=True,
    root_all_changed_assertion_scopes_read=True, root_all_actual_gate_adapters_and_TYPE_review_read=True,
    independent_review_sha256=expected_review, all_generic_guard_families_retained=True,
    ten_fragment_metadata_owners_and_all_six_body_binder_guards=True,
    introduced_type_entries=23, restricted_recursive_calls=7, termination_by_clauses=3,
    target_source_lines=410, whole_selected_source_hard_stop=430,
    actual_metadata_cut_jobs=23, actual_failed_metadata_jobs=1,
    standalone_cwd='/', both_modes_required_before_proof_commit=True,
    new_Lean_Lake_jobs_authorized=0, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed complete source-reviewed verifier and actual data; both saved modes authorized.')
