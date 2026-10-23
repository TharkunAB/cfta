exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import ast
import collections
import re
import sys

owner_path, owner_pins, owner_freeze, peer_path, peer_pins, peer_freeze, peer_review = sys.argv[1:]
owner, peer = Path(owner_path), Path(peer_path)
checked_package(owner, owner_pins, owner_freeze)
checked_package(peer, peer_pins, peer_freeze)
assert sha(peer / 'review.json') == peer_review and load(peer / 'review.json')['status'] == 'CLEAR'
source, data = [owner / name for name in ['verify-proofs.py', 'bound-data.json']]
assert len(source.read_bytes().splitlines()) == 424 and len(data.read_bytes().splitlines()) == 530
assert not re.search(rb'__H\d+_', data.read_bytes())
assert sha(data).encode() in source.read_bytes()
tests = collections.Counter(ast.unparse(node.test) for node in ast.walk(ast.parse(source.read_bytes())) if isinstance(node, ast.Assert))
assert sum(tests.values()) == 224
crosswalk = load(HERE / 'verifier-scope-plan/guard-crosswalk.json')
generic = collections.Counter(row['basis_expression'] for row in crosswalk['rows'] if row['action'] == 'KEEP_GENERIC_GUARD_EXACT_EXPRESSION')
assert sum(generic.values()) == 174 and not (generic - tests)
bound = load(data)
for key in ['history_review', 'history_peer']:
    item = bound[key]
    path = HERE / item['path']
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
assert all(not (HERE / name).exists() for name in ['verify-proofs.py', 'bound-data.json'])
archive(owner, 'proof-verifier-preparation')
archive(peer, 'proof-verifier-audit')
for name in ['verify-proofs.py', 'bound-data.json']:
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'), bound_data_sha256=sha(HERE / 'bound-data.json'),
    independent_review_sha256=peer_review, root_complete_selected_code_lines_read=424,
    root_complete_bound_data_lines_read=530, root_complete_basis_lines_read=418,
    root_draft_plus_exact_actual_history_pin_and_digest_delta_read=True,
    all_generic_174_assertions_exact=True, all_47_scope_adapters_reviewed=True,
    whole_source_hard_stop=430, actual_assertions=224, no_extra_proof_job=True,
    actual_public_TYPE_raw_booleans=[True, True, True],
    full_generalized_IH_and_five_equation_types_retained=True,
    external_qualified_native_dependency_only_token_view_guarded=True,
    external_dependency_requires_exact_reviewed_command_line=True,
    prior_preparation_source_review_rejection_retained=True,
    standalone_normal_and_live_from_cwd_slash_authorized=True,
    proof_commit_and_document_write_require_both_actual_mode_PASS=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('Installed the complete reviewed saved verifier and actual bound data. Standalone dual-mode execution is authorized.')
