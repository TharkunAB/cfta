exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
packages = [
    ('document-preparation', 'fe30c496a751bd703d1de9b1ecdf1871c69959d7eb066f1238ca135f8bc62ac2', 'a41c32a4ab4498e392f0fb42ea539924092c9f8c86964b2bc1617aa2f50d954b'),
    ('publication-preparation', '4dd3cb90612024e1f03d6208a2d0bf7a5946cc029a5b71b8de1bc419bbaf6af0', '8d0b4af2a76c284ddac8e75dae2a9bc771b3d4fbef20bfdc8868b680a2a6b41b'),
    ('document-audit', 'f525e42d55c8364012534841533adb3d5f26d98e15398b16f9045928ff3bfede', 'af18b92bfd311da31b892462d44d0f247464ea1bf443ee8df3be1b9dc3a2a263'),
    ('publication-audit', '3e15499e797b1a7fdc7e9946ba214062c3b02a74cf4b30bbcba3debe1af53375', 'a050a24d18a08206b78575393123d92ce4d1473681aef69a93be7b3d886e93fb')]
for name, pins, freeze in packages:
    path = Path('/tmp/mcfta-pair-inventory-rebase-' + name)
    checked_package(path, pins, freeze)
    if name.endswith('audit'):
        assert load(path / 'review.json')['status'] == 'CLEAR'
    archive(path, name)
installed = {}
for name, owner in [('update-documents.py', 'document-preparation'),
        ('proof-commit.py', 'publication-preparation'), ('final-publication.py', 'publication-preparation'),
        ('run-standalone-proof-evidence.py', 'publication-preparation')]:
    target = HERE / name
    assert not target.exists()
    target.write_bytes((HERE / owner / name).read_bytes())
    installed[name] = sha(target)
save('root-document-source-review.json', dict(status='ACCEPTED_WHOLE_DOCUMENT_WRITER_AND_TEMPLATES',
    root_whole_selected_source_lines_read=88, root_whole_basis_and_deltas_read=True,
    whole_templates_read=True, independent_review_sha256=sha(HERE / 'document-audit/review.json'),
    installed_tools={'update-documents.py': installed.pop('update-documents.py')},
    nine_LF_inverses=True, haskell_repair_index_first=True, requires_actual_dual_mode_and_proof_commit=True,
    goal_status='ACTIVE_INCOMPLETE'))
save('root-publication-source-review.json', dict(status='ACCEPTED_WHOLE_LOCAL_PUBLICATION_AND_STANDALONE_PROGRAMS',
    root_whole_selected_source_lines_read=101, root_whole_basis_and_deltas_read=True,
    installed_tools=installed, independent_review_sha256=sha(HERE / 'publication-audit/review.json'),
    proof_commit_requires_actual_dual_mode_PASS=True, proof_file_count=2,
    publisher_requires_final_root_gate_and_seal=True, publisher_network_commands=0,
    authorized_root_push_separate=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed source-reviewed document, commit, saved-mode and local publication tools; none executed.')
