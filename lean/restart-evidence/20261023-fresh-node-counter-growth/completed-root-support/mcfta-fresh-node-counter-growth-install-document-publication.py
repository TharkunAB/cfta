exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import sys
document_pins, document_freeze, document_review, publication_pins, publication_freeze, publication_review = sys.argv[1:]
packages = [
    ('document-preparation', '80122697fc33cb69c9a51d94d09a26a872e0d2c101ad33f875595821c7147b11', '5cf3a95521878460753d61eec442b34352cddd41465b4a92b9b5e20b44d7541b', None),
    ('publication-preparation', 'e9bdb9fe1a53b20d418cd0b8affbd54dc58706d031e24c4c5b3f24019be5e879', 'a7c191b66e87c900076c8ed38543a93efd8e98a7fbe05f62e33cbab7430a84c5', None),
    ('document-audit', document_pins, document_freeze, document_review),
    ('publication-audit', publication_pins, publication_freeze, publication_review)]
for name, pins, freeze, review_sha in packages:
    path = Path('/tmp/mcfta-fresh-node-counter-growth-' + name)
    checked_package(path, pins, freeze)
    if review_sha is not None:
        assert sha(path / 'review.json') == review_sha
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
    whole_templates_read=True, independent_review_sha256=document_review,
    installed_tools={'update-documents.py': installed.pop('update-documents.py')},
    nine_LF_inverses=True, haskell_repair_index_first=True, requires_actual_dual_mode_and_proof_commit=True,
    goal_status='ACTIVE_INCOMPLETE'))
save('root-publication-source-review.json', dict(status='ACCEPTED_WHOLE_LOCAL_PUBLICATION_AND_STANDALONE_PROGRAMS',
    root_whole_selected_source_lines_read=101, root_whole_basis_and_deltas_read=True,
    installed_tools=installed, independent_review_sha256=publication_review,
    proof_commit_requires_actual_dual_mode_PASS=True, proof_file_count=2,
    publisher_requires_final_root_gate_and_seal=True, publisher_network_commands=0,
    authorized_root_push_separate=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed source-reviewed document, commit, saved-mode and local publication tools; none executed.')
