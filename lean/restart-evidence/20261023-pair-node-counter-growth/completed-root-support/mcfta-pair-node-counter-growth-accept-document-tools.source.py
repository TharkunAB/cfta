exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-pair-node-counter-growth-document-preparation-v2')
peer = Path('/tmp/mcfta-pair-node-counter-growth-document-tool-review-v2')
checked_package(owner,'238332b405ae2c6708943d4ca54fba0f994c197e72bfa9fdb4c5a5f7737f2b18','9ecb21a3bb3800852b7ad5381018c343aebc0e548154e4efd921a937e550117e')
checked_package(peer,'4e19dafacce63b63f634dbbfe9424c9eab9e2b472894821f4c2d0e5fc61c63cb','ba3d55b49414bd839c7e49bb1a8730d487f56413814df0de06639cba41d15368')
assert sha(peer / 'review.json') == 'a1e03387a3274118bcac701fdca512a77b11cdd1a179b7bf1e7e67faf5729c2e'
assert load(peer / 'review.json')['status'] == 'CLEAR'
writer = owner / 'update-documents.py'
assert sha(writer) == '4c043bbdf96e6859b1a6818993398142220f961482a0614ea0d1cd06c6c60a27'
assert len(writer.read_bytes().splitlines()) == 88
assert sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(writer.read_text()))) == 25
assert writer.read_bytes() == (owner / 'original-v1/update-documents.py').read_bytes()
assert not (HERE / 'update-documents.py').exists()
archive(owner,'document-preparation')
archive(peer,'document-source-audit')
(HERE / 'update-documents.py').write_bytes(writer.read_bytes())
save('root-document-source-review.json',dict(status='ACCEPTED_COMPLETE_DOCUMENT_WRITER_AND_TEMPLATES',
    independent_review_sha256=sha(peer / 'review.json'),root_whole_selected_and_basis_lines_read=88,
    root_whole_forward_inverse_diffs_and_both_templates_read=True,assertions_retained=25,
    installed_sha256=sha(HERE / 'update-documents.py'),nine_LF_prefix_inverses=True,
    FINDINGS_repair_index_first=True,dual_saved_modes_before_proof_commit_and_documents=True,
    document_execution_authorized_after_actual_both_modes_and_exact_proof_commit=True,
    V2_only_two_preservation_phrase_corrections_and_complete_V1_retained=True,
    no_future_execution_outcome_claimed=True,goal_status='ACTIVE_INCOMPLETE'))
print('Installed the reviewed writer and V2 payloads. Execution requires both saved reports and the actual proof commit.')
