exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import ast
import collections
import sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
owner = Path('/tmp/mcfta-native-node-counter-growth-proof-verifier-source')
peer = Path('/tmp/mcfta-native-node-counter-growth-proof-verifier-audit')
checked_package(owner, 'b3a570e66f4a8a1487521999473f39a6becf698e651e681108c814ac4c8e1c6b', '180390bc05ed24c036a183e455bb10a6de563f3c83af2d54d986cc234d33dec9')
checked_package(peer, expected_pins, expected_freeze)
assert sha(peer / 'review.json') == expected_review and load(peer / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'verify-proofs.py') == '1c1be9c5ad2b6723e33b9acb38690ab27a1388b87dd565cc017723f69afd9440'
assert sha(owner / 'bound-data.json') == 'a6cdede0a991e2dd3afba59e8feb0e818b51938c860fef2a5dae0c55b0bb995e'
assert len((owner / 'verify-proofs.py').read_bytes().splitlines()) == 418
assert len((owner / 'bound-data.json').read_bytes().splitlines()) == 522
tree = ast.parse((owner / 'verify-proofs.py').read_bytes())
tests = collections.Counter(ast.unparse(node.test) for node in ast.walk(tree) if isinstance(node, ast.Assert))
assert sum(tests.values()) == 221
crosswalk = load(HERE / 'verifier-scope-plan/guard-crosswalk.json')
generic = collections.Counter(row['basis_expression'] for row in crosswalk['rows'] if row['action'] == 'KEEP_GENERIC_GUARD')
assert sum(generic.values()) == 174 and not (generic - tests)
for entry in load(owner / 'input-references.json'):
    path = HERE / entry['path']
    assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256']
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
assert all(not (HERE / name).exists() for name in ['verify-proofs.py', 'bound-data.json'])
archive(owner, 'proof-verifier-preparation')
archive(peer, 'proof-verifier-audit')
for name in ['verify-proofs.py', 'bound-data.json']:
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'), bound_data_sha256=sha(HERE / 'bound-data.json'),
    independent_review_sha256=expected_review, root_complete_selected_code_lines_read=418,
    root_complete_bound_data_lines_read=522, root_complete_basis_lines_read=404,
    root_draft_416_plus_exact_two_line_history_pin_and_digest_delta_read=True,
    all_generic_174_assertions_exact=True, all_38_scope_adapters_reviewed=True,
    whole_source_hard_stop=430, actual_assertions=221, no_extra_proof_job=True,
    actual_public_TYPE_raw_booleans=[True, False, False],
    full_generalized_IH_and_six_equation_types_retained=True,
    standalone_normal_and_live_from_cwd_slash_authorized=True,
    proof_commit_and_document_write_require_both_actual_mode_PASS=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('Installed the complete reviewed saved verifier and actual bound data. Standalone dual-mode execution is authorized.')
