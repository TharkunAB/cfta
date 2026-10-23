exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
packages = [
    ('/tmp/mcfta-cluster-admission-closing-preparation', '09a483893ab5f850737e1e113d7a881d6df1b8dc91e1e28a419bf598cad4c4fd', '1793e22ab82c6f2bcbc4138b0800e51c9fea63eef0a2e0eee6e754ca3654527e', 'closing-preparation'),
    ('/tmp/mcfta-cluster-admission-closing-tools-audit', '9ab42e5a5f74ce0cc31a606c379e9a099f2c8ae18d4e8cb5db01f278599eda24', '44201084903739b276ae0d6e877477b8f317e27947f40dcefd449d8a06c41aae', 'closing-tools-audit'),
    ('/tmp/mcfta-cluster-admission-document-preparation', 'f0910d80fea18bb2fd195aea2c2e890650c1daeacbe2bbab1883c7be98494bf3', 'a5c551b1fbaa2cae93e1f9819aacc1034e2658c7605c1cd90b1f5886c67cb39e', 'document-preparation'),
    ('/tmp/mcfta-cluster-admission-document-source-audit', '0e5a2f6de25c8a74537b97203e5575b5b47c691173bc7255d44c9291534a759d', '7c8a300c92e3a039d2fb4f7b7aa0cd1148b3c126cbc76e8f212ffac7757e2f5f', 'document-source-audit'),
]
for path, pins, frozen, _archive_name in packages:
    checked_package(Path(path), pins, frozen)
assert load(Path(packages[1][0]) / 'review.json')['status'] == 'CLEAR'
assert load(Path(packages[3][0]) / 'review.json')['status'] == 'SOURCE_ONLY_CLEAR'
for path, _pins, _frozen, archive_name in packages:
    archive(Path(path), archive_name)
installed = {}
for name, digest in [
    ('verify-preservation.py', '67fad07c7459cb6cc43ecc0619fd93da7dd49df1f32ee1abbbddccd215460c50'),
    ('archive-support.py', '8fbb41ff4ff0c1e54586d5923d5ae8e4bb4729db4e9987908060451fd5b78b75'),
    ('seal-checkpoint.py', '04e25334489ac1fd9cd12a8d71ff888dc71db3ca36011bb9d5223e138ebb72b7'),
    ('verify-seal.py', '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7'),
    ('verify-checkpoint.py', '51586c42b9e9f064cba242b1fe3abe9259d0c745ecebcc3cdc91e99e278410f9'),
]:
    source = Path(packages[0][0]) / 'selected' / name
    assert sha(source) == digest and not (HERE / name).exists()
    shutil.copy2(source, HERE / name)
    installed[name] = sha(HERE / name)
writer = Path(packages[2][0]) / 'update-documents.py'
assert sha(writer) == '590e6154608b461632d454dbf1dd97f86f4b1e68b0a574fd91545e01d1da4688'
assert not (HERE / 'update-documents.py').exists()
shutil.copy2(writer, HERE / 'update-documents.py')
save('root-closing-tools-review.json', {
    'status': 'ACCEPTED_REVIEWED_TOOLS_INSTALLED_WITH_ORDERED_ACTIVATION',
    'root_whole_selected_lines_read': 240, 'root_whole_predecessor_lines_read': 229,
    'independent_review_sha256': sha(HERE / 'closing-tools-audit/review.json'),
    'installed_tools': installed,
    'activation_order': ['dual-mode standalone proof evidence', 'four-file proof commit', 'documents', 'independent final documents and preservation', 'one-time support', 'seal mandatory verification rerun', 'local-only publication', 'authorized root push'],
    'no_execution_result_claimed': True,
})
save('root-document-source-review.json', {
    'status': 'ACCEPTED_DOCUMENT_WRITER_AFTER_DUAL_MODE_PROOF_AND_FOUR_FILE_COMMIT',
    'root_whole_writer_lines_read': 89, 'root_complete_templates_read': True,
    'writer_sha256': sha(HERE / 'update-documents.py'),
    'independent_review_sha256': sha(HERE / 'document-source-audit/review.json'),
    'FINDINGS_repair_index_first': True, 'exact_old_text_inverses': 9,
    'whole_goal_complete': False, 'writer_has_not_run': True,
})
print('PASS: reviewed closing tools and document writer installed; execution order remains gated')
