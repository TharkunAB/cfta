exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
packages = [
    ('document-preparation', '1b748420766994c32f7b05b4f4d83dd9ae60f9f66a1c2dbf033438ac6b0cd379', '3cc1f21137014c3bd8256a08ca62f5cad9dfb60a243b344af3a348d0944a27ed'),
    ('publication-preparation', 'd782b9b86a289850373de0f983b1ba2ddc577e0ddf8259e7ad7b8213856adc38', 'f70edc0aae3d7e47b6d9366097c0fbe696430faa00497c6835d9ef03a0ca674a'),
    ('document-source-audit', 'cf98d0d60e5a83d979090e28666bb20f66e6cbc8c70917f8fd274fb1044fc28b', '9030866a4ef02d15df4483f139619def7d85a373729da956959cf51c2abd10b5'),
    ('publication-source-audit', '67cedb4698531460449db62ac69cc731559f26743dde1c69ef17468f6dad3ac1', 'dac04bb2ba3b713040bdd759c8beaeb61a8a1b4479c1dc9c75e217d417174959')]
for name, pins, freeze in packages:
    path = Path('/tmp/mcfta-rebuild-admission-' + name)
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
    whole_templates_read=True, independent_review_sha256=sha(HERE / 'document-source-audit/review.json'),
    installed_tools={'update-documents.py': installed.pop('update-documents.py')},
    nine_LF_inverses=True, haskell_repair_index_first=True, requires_actual_dual_mode_and_proof_commit=True,
    goal_status='ACTIVE_INCOMPLETE'))
save('root-publication-source-review.json', dict(status='ACCEPTED_WHOLE_LOCAL_PUBLICATION_AND_STANDALONE_PROGRAMS',
    root_whole_selected_source_lines_read=101, root_whole_basis_and_deltas_read=True,
    installed_tools=installed, independent_review_sha256=sha(HERE / 'publication-source-audit/review.json'),
    proof_commit_requires_actual_dual_mode_PASS=True, proof_file_count=2,
    publisher_requires_final_root_gate_and_seal=True, publisher_network_commands=0,
    authorized_root_push_separate=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed source-reviewed document, commit, saved-mode and local publication tools; none executed.')
