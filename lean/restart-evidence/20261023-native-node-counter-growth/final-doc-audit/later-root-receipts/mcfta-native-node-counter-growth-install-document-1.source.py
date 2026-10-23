exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import ast
owner = Path('/tmp/mcfta-native-node-counter-growth-document-preparation')
peer = Path('/tmp/mcfta-native-node-counter-growth-document-tool-audit')
checked_package(owner, '51bf170e46d191d14785d4bb8fc19ce0f4d9725d95744f1c7488f67268421898', '71cf1c7207e8a788a96f46901990cf2fed78b10798e1bb59ea7d697102990714')
checked_package(peer, 'c20a849c3e31c88e0485d1e12620e408e17878f080659cc0b6c0fa8c515b8e80', '40ab8c2f0bc3e6a9c532934ec39308cd0cc35b565f6acee567a5559561cf4015')
assert load(peer / 'review.json')['status'] == 'CLEAR'
assert len((owner / 'update-documents.py').read_bytes().splitlines()) == 88
assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse((owner / 'update-documents.py').read_bytes()))) == 25
assert not (HERE / 'update-documents.py').exists()
archive(owner, 'document-preparation')
archive(peer, 'document-tool-audit')
(HERE / 'update-documents.py').write_bytes((owner / 'update-documents.py').read_bytes())
save('root-document-source-review.json', dict(status='ACCEPTED_COMPLETE_DOCUMENT_WRITER_AND_TEMPLATES',
    independent_review_sha256=sha(peer / 'review.json'), root_whole_selected_and_basis_lines_read=88,
    root_whole_forward_inverse_diffs_and_both_templates_read=True, assertions_retained=25,
    installed_sha256=sha(HERE / 'update-documents.py'), nine_LF_prefix_inverses=True,
    FINDINGS_repair_index_first=True, dual_saved_modes_before_proof_commit_and_documents=True,
    document_execution_authorized_after_actual_both_modes_and_exact_proof_commit=True,
    no_future_execution_outcome_claimed=True, goal_status='ACTIVE_INCOMPLETE'))
print('Installed the reviewed document writer and conditional templates. Proof evidence and proof commit must precede execution.')
