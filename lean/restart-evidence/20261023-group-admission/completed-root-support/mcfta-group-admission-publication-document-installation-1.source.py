exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-group-admission-document-preparation')
audit = Path('/tmp/mcfta-group-admission-document-source-audit')
checked_package(owner, '59bbde54f2069a8265015161d6854eb49f009f2556b5e0ad1199f308910281e9', 'd567a561c7b10645dcd6b1510ee801ade5269deb2e95ad6cb859f49e882ba245')
checked_package(audit, '02c318adb471c341213398da04a8d9463db28b7d57142a64b2e5280717aa4e3b', '23ccd3c6833149dd3909555aa75147459a8e8cf28bc562be5a10cace961aee4b')
assert sha(audit / 'review.json') == 'd9b641c99dfd3fbafdd3c8c7bc17a5f4a139c0dde227827e25578976f742b57f'
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'update-documents.py') == 'fe1376bf0b25182069d1cbdb53ae53e742ba084eb1b5b9c4107fa67f8ec3815a'
assert not (HERE / 'update-documents.py').exists()
archive(owner, 'document-preparation')
archive(audit, 'document-source-audit')
(HERE / 'update-documents.py').write_bytes((owner / 'update-documents.py').read_bytes())
save('root-document-source-review.json', dict(status='ACCEPTED_WHOLE_DOCUMENT_WRITER_AND_TEMPLATES',
    root_whole_selected_writer_lines_read=88, root_whole_basis_lines_read=89,
    root_whole_templates_read=True, writer_sha256=sha(HERE / 'update-documents.py'),
    independent_review_sha256=sha(audit / 'review.json'),
    both_saved_modes_and_exact_proof_commit_required_before_document_writes=True,
    all_nine_prewrite_prefix_inverses=True, findings_repair_index_first=True))
owner = Path('/tmp/mcfta-group-admission-publication-preparation')
audit = Path('/tmp/mcfta-group-admission-publication-source-audit')
checked_package(owner, '96bc64b087f90086f43fd66c5125a0cc2ae65727149f07b5d3ba1cde17e99d78', 'a7b1d06867aaef69976035dc342255fa10f55fb1a63ebff9a6f910bdfcde3a3f')
checked_package(audit, '34064522799db7f1689e91a1a467ff8abdc06769b716d78179f72cc9ca799f3f', 'e5a5f592708ccfecb63e5b89b0f6c4a185515e9f200c0305b2d025e89ddb05db')
assert sha(audit / 'review.json') == '86f130cb9e25fd6f09b9a7a4f068537114d33dedad84f06f9c5f265e4d826471'
assert load(audit / 'review.json')['status'] == 'CLEAR'
names = ['proof-commit.py', 'final-publication.py', 'run-standalone-proof-evidence.py']
assert sum(len((owner / name).read_bytes().splitlines()) for name in names) == 101
assert all(not (HERE / name).exists() for name in names)
archive(owner, 'publication-preparation')
archive(audit, 'publication-source-audit')
for name in names:
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-publication-source-review.json', dict(status='ACCEPTED_WHOLE_LOCAL_PUBLICATION_AND_STANDALONE_PROGRAMS',
    root_whole_selected_source_lines_read=101, root_whole_basis_and_deltas_read=True,
    installed_tools={name:sha(HERE / name) for name in names},
    independent_review_sha256=sha(audit / 'review.json'),
    proof_commit_requires_actual_dual_mode_PASS=True, proof_file_count=2,
    publisher_requires_final_root_gate_and_seal=True, publisher_network_commands=0,
    authorized_root_push_separate=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed whole-reviewed document, proof-commit, standalone and local publication programs.')
