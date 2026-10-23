exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import ast, sys
owner = Path('/tmp/mcfta-stored-node-counter-growth-proof-verifier-source')
review = Path('/tmp/mcfta-stored-node-counter-growth-proof-verifier-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, 'f3b68135659d6a87e08f1c2bdde04752ca2843be669c7a8abb2874c1a51755a2', '8c41219df3bcb77643025a13d5b51d9c934ea3350245f13af0405933cd71dd19')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
code = (owner / 'verify-proofs.py').read_bytes()
assert len(code.splitlines()) == 404
assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(code))) == 212
assert len((owner / 'bound-data.json').read_bytes().splitlines()) == 483
assert sha(HERE / 'source-history-gate.json') == '124b9bed8354602aa8e01a18373234324511f6c410c723aa460adef1347479e6'
archive(owner, 'proof-verifier-preparation')
archive(review, 'proof-verifier-audit')
for name, expected in [('verify-proofs.py', 'a15458cb2d18eb7519e34383868cc4329165ae9188784cf484e8711e0c8b12ba'),
        ('bound-data.json', 'f60555dd0c4e55bdea653c5ef62cb554e9ffe5fe2ff07a3d07adec264150fc66')]:
    assert not (HERE / name).exists() and sha(owner / name) == expected
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'), bound_data_sha256=sha(HERE / 'bound-data.json'),
    root_whole_selected_code_lines_read=404, root_whole_actual_bound_data_lines_read=483,
    root_whole_basis_previously_reviewed=True, root_whole_adaptation_diff_read=True,
    root_all_changed_assertion_scopes_read=True, root_all_actual_gate_adapters_and_TYPE_review_read=True,
    independent_review_sha256=expected_review, all_generic_guard_families_retained=True,
    eight_fragment_metadata_owners_and_all_six_body_binder_guards=True,
    introduced_type_entries=7, restricted_recursive_calls=0, termination_by_clauses=0,
    case_pattern_groups_and_acyclic_earlier_theorem_calls_checked=True, early_canonical_copy_retained=True,
    target_source_lines=410, whole_selected_source_hard_stop=430,
    actual_metadata_cut_jobs=13, actual_failed_metadata_jobs=0, standalone_cwd='/',
    both_modes_required_before_proof_commit=True, new_Lean_Lake_jobs_authorized=0, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed complete source-reviewed verifier and actual data; both saved modes authorized.')
