exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
doc = Path('/tmp/mcfta-stored-node-counter-growth-document-preparation')
pub = Path('/tmp/mcfta-stored-node-counter-growth-publication-preparation')
peer = Path('/tmp/mcfta-stored-node-counter-growth-document-publication-audit')
checked_package(doc, '0ea345b72d5d01aa326da4fdee037f86bc433fa80fa3c1539cb4b574ae6a0356', '0fa8e6ef6b42403da033a5c4c46166fdd1199293de7779c5e2fa030094bea9c8')
checked_package(pub, '5ce314a7c93a80c21786a08c4802a56f1355be3a96d40b45850cd6ae1222b75b', '8052476449e034b93dfb66fb38f3e566eb13bcec1a8342a2fe291e881952e4ed')
checked_package(peer, '3d36984a44cd096dc8ded2527fac905af038277de8157b68b155b16ceff4fdee', 'f26ba2bb2b9a2e041a85f57c5fd064eb4c980900c0772dfb756cbeb867941f53')
assert sha(peer / 'review.json') == '9910e835ea3867d41abb77f391409f913eff0530ae2b3e9dd4d7a28a121b0a8b'
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and review['checks']['all69_AST_assertions_retained']
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
archive(doc, 'document-preparation')
archive(pub, 'publication-preparation')
archive(peer, 'document-publication-audit')
installed = {}
for owner, name, digest in [(doc, 'update-documents.py', 'efdb1de5bce28f396d51ff9432034b16b8c336b134475a092b13f8c3e3e4b81e'),
        (pub, 'proof-commit.py', 'd15d500dee1cfc40c8245a5f74facc158ea2337cca32b00ffb7bd9095da8a26a'),
        (pub, 'final-publication.py', '7e16f269af39496cd61a9ad6dcb0ff09e3f7874757f8f24d83b27ead22ed8b73'),
        (pub, 'run-standalone-proof-evidence.py', 'd082afff095abfcfd0f2e581d90ad7445e8bbadde021d53e5668570188d782f7')]:
    assert not (HERE / name).exists() and sha(owner / name) == digest
    (HERE / name).write_bytes((owner / name).read_bytes())
    installed[name] = digest
save('root-document-publication-source-review.json', dict(status='ACCEPTED_COMPLETE_FOUR_TOOLS_AND_TEMPLATES',
    independent_review_sha256=sha(peer / 'review.json'), root_all_189_selected_and_basis_lines_read=True,
    root_whole_exact_diffs_and_both_templates_read=True, all_69_assertions_retained=True,
    installed=installed, nine_LF_prefix_inverses=True, FINDINGS_repair_index_first=True,
    dual_saved_modes_before_proof_commit_and_documents=True, exact_two_file_proof_commit=True,
    local_publisher_network_free=True, full_blob_mode_and_sealed_index_checks_retained=True,
    future_execution_outcomes_claimed=False, standalone_authorized_after_verifier_gate=True,
    proof_commit_authorized_after_actual_both_modes=True, document_writes_authorized_after_proof_commit=True,
    local_publication_authorized_after_final_review_and_seal=True, goal_status='ACTIVE_INCOMPLETE'))
print('Installed exact reviewed document and publication tools; prerequisite gates remain mandatory.')
