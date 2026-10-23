exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import ast
import sys

peer_pins, peer_freeze, peer_review = sys.argv[1:]
owner = Path('/tmp/mcfta-demand-node-counter-growth-document-preparation')
peer = Path('/tmp/mcfta-demand-node-counter-growth-document-tool-audit')
checked_package(owner, '4782dbb7b932f47ea2d4bbb9350467a283a596e0ea5bfede891f8eb9ea2ab872', '2cae9396bc0c9b271b7e64f1f057524283529ff0b83d8595df933c8f842a4ebe')
checked_package(peer, peer_pins, peer_freeze)
assert sha(peer / 'review.json') == peer_review and load(peer / 'review.json')['status'] == 'CLEAR'
source = owner / 'update-documents.py'
assert len(source.read_bytes().splitlines()) == 88
assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(source.read_bytes()))) == 25
assert not (HERE / 'update-documents.py').exists()
archive(owner, 'document-preparation')
archive(peer, 'document-tool-audit')
(HERE / 'update-documents.py').write_bytes(source.read_bytes())
save('root-document-source-review.json', dict(status='ACCEPTED_COMPLETE_DOCUMENT_WRITER_AND_TEMPLATES',
    independent_review_sha256=peer_review, root_whole_selected_and_basis_lines_read=88,
    root_whole_forward_inverse_diffs_and_both_templates_read=True, assertions_retained=25,
    installed_sha256=sha(HERE / 'update-documents.py'), nine_LF_prefix_inverses=True,
    FINDINGS_repair_index_first=True, dual_saved_modes_before_proof_commit_and_documents=True,
    document_execution_authorized_after_actual_both_modes_and_exact_proof_commit=True,
    no_future_execution_outcome_claimed=True, goal_status='ACTIVE_INCOMPLETE'))
print('Installed the reviewed document writer and conditional templates. Actual saved checks and proof commit must precede execution.')
