exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import ast
for label, owner_pins, owner_freeze, peer_path, peer_pins, peer_freeze, names, lines, assertions in [
    ('closing', '31c4f6b6ede66cc4a1937e4ba18537129bf50ac0554239c285044673288a6414', '3ec96d5897c68f4d6bf76e7dce234f583c8dd47771e9d44d6e3aed50833f7ee1', 'closing-actual-audit', 'ad5adc416b621501b42037c1a16a0701313f0f30d7dd277c5f1fef29474aabae', 'e00db71899a4ba68368e744fe87553dc1b499a13f8f47bbed7ab877deec03cdd', ['verify-preservation.py', 'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'verify-checkpoint.py'], 236, 59),
    ('publication', 'c2f1e54544ca8b2f3586bf4cfbdd7cfefe253ccfec99b004f657fd9b6c0076d0', '0f7fa10a9c8ef70cc4a753625c325ddb8b9ead79f4b103a29fec6d66318d0b8b', 'publication-audit', 'dc97d410bcad874513b68a12cadf761b418e52d7637bc6a451687a6a83ce9770', 'f4511a700ba218aebe589e400b2324596a91034ed1ca63734646f932e7d5178d', ['run-standalone-proof-evidence.py', 'proof-commit.py', 'final-publication.py'], 101, 44)
]:
    owner = Path('/tmp/mcfta-native-node-counter-growth-' + label + '-actual')
    peer = Path('/tmp/mcfta-native-node-counter-growth-' + peer_path)
    checked_package(owner, owner_pins, owner_freeze)
    checked_package(peer, peer_pins, peer_freeze)
    assert load(peer / 'review.json')['status'] == 'CLEAR'
    bindings = load(owner / 'bindings.json')
    assert bindings['actual_proof_cut']['sha256'] == sha(HERE / 'actual-proof-cut.json')
    for entry in bindings['external_references']:
        path = Path(entry['path'])
        assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256']
    selected = owner / 'selected' if label == 'closing' else owner
    assert sum(len((selected / name).read_bytes().splitlines()) for name in names) == lines
    assert sum(isinstance(node, ast.Assert) for name in names for node in ast.walk(ast.parse((selected / name).read_bytes()))) == assertions
    assert all(not (HERE / name).exists() for name in names)
    if label == 'closing':
        assert (selected / 'verify-seal.py').read_bytes() == (owner / 'pending-preparation/basis/verify-seal.py').read_bytes()
        assert load(HERE / 'root-closing-scope-gate.json')['selected_authorship_authorized']
    archive(owner, label + '-preparation')
    archive(peer, label + '-tool-audit')
    for name in names:
        (HERE / name).write_bytes((selected / name).read_bytes())
    save('root-' + label + '-tools-review.json', dict(status='ACCEPTED_COMPLETE_FIVE_CLOSING_TOOLS' if label == 'closing' else 'ACCEPTED_COMPLETE_THREE_LOCAL_PUBLICATION_TOOLS',
        independent_review_sha256=sha(peer / 'review.json'), root_complete_selected_and_basis_lines_read=lines,
        root_whole_forward_diffs_and_actual_data_binding_read=True, assertions=assertions,
        all_generic_AST_structure_and_guards_retained=True, no_new_guard_exception=True,
        installed={name: sha(HERE / name) for name in names}, mandatory_checkpoint_before_seal=True,
        support_collection_once=True, support_self_exclusion='mcfta-native-node-counter-growth-support-1',
        dual_saved_modes_before_proof_commit_and_documents=True, exact_two_file_proof_commit=True,
        local_publisher_network_free=True, full_blob_mode_and_sealed_index_checks_retained=True,
        standalone_authorized_after_verifier_gate=True, proof_commit_authorized_after_actual_both_modes=True,
        support_and_seal_after_final_review=True, local_publication_authorized_after_final_review_and_seal=True,
        no_future_execution_outcome_claimed=True, goal_status='ACTIVE_INCOMPLETE'))
print('Installed the eight complete reviewed closing and local publication tools. All execution prerequisites remain.')
