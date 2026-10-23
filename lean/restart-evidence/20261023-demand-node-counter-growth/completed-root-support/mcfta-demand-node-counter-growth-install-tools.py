exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import ast
import sys

label, peer_path, peer_pins, peer_freeze, peer_review = sys.argv[1:]
assert label in ['closing', 'publication']
if label == 'closing':
    owner = Path('/tmp/mcfta-demand-node-counter-growth-closing-actual')
    owner_pins = '234828d4038987541691108dd4a3479b36e51b2561b3f4e168c762198dce052f'
    owner_freeze = 'a9a77bee96b6703e29e516a52cb84b1a520a4bf8058acef3e0e5210c5ef41c11'
    names = ['verify-preservation.py', 'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'verify-checkpoint.py']
    lines, assertions = 236, 59
else:
    owner = Path('/tmp/mcfta-demand-node-counter-growth-publication-preparation')
    owner_pins = 'eeeeaa37a37b5197897c59b31b41317f2dbddb75504d5ec205bf402d73005e68'
    owner_freeze = '3babeb72fa200152ddb3f60a3a4730fd458b6397d4592cae78dfad7f417a1ae0'
    names = ['run-standalone-proof-evidence.py', 'proof-commit.py', 'final-publication.py']
    lines, assertions = 101, 44
peer = Path(peer_path)
checked_package(owner, owner_pins, owner_freeze)
checked_package(peer, peer_pins, peer_freeze)
assert sha(peer / 'review.json') == peer_review and load(peer / 'review.json')['status'] == 'CLEAR'
selected = owner / 'selected'
assert sum(len((selected / name).read_bytes().splitlines()) for name in names) == lines
assert sum(isinstance(node, ast.Assert) for name in names for node in ast.walk(ast.parse((selected / name).read_bytes()))) == assertions
assert all(not (HERE / name).exists() for name in names)
assert load(HERE / ('root-' + label + '-scope-gate.json'))['selected_authorship_authorized']
if label == 'closing':
    assert (selected / 'verify-seal.py').read_bytes() == (owner / 'pending-preparation/basis/verify-seal.py').read_bytes()
    for entry in load(owner / 'external-input-pins.json'):
        path = Path(entry['path'])
        assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256']
    for name, data in load(owner / 'selected-scripts.json').items():
        assert data['actual_sha256'] == sha(selected / name)
        if name != 'verify-checkpoint.py':
            assert (selected / name).read_bytes() == (owner / 'pending-preparation/selected' / name).read_bytes()
else:
    assert load(owner / 'actual-bindings.json')['actual_proof_cut_sha256'] == sha(HERE / 'actual-proof-cut.json')
    assert load(owner / 'actual-bindings.json')['common_helper_sha256'] == sha(HERE / 'root-common.py')
archive(owner, label + '-preparation')
archive(peer, label + '-tool-audit')
for name in names:
    (HERE / name).write_bytes((selected / name).read_bytes())
save('root-' + label + '-tools-review.json', dict(status='ACCEPTED_COMPLETE_FIVE_CLOSING_TOOLS' if label == 'closing' else 'ACCEPTED_COMPLETE_THREE_LOCAL_PUBLICATION_TOOLS',
    independent_review_sha256=peer_review, root_complete_selected_and_basis_lines_read=lines,
    root_whole_forward_diffs_and_actual_data_binding_read=True, assertions=assertions,
    all_generic_AST_structure_and_guards_retained=True, no_new_guard_exception=True,
    installed={name: sha(HERE / name) for name in names}, mandatory_checkpoint_before_seal=True,
    support_collection_once=True, support_self_exclusion='mcfta-demand-node-counter-growth-support-1',
    dual_saved_modes_before_proof_commit_and_documents=True, exact_two_file_proof_commit=True,
    local_publisher_network_free=True, full_blob_mode_and_sealed_index_checks_retained=True,
    standalone_authorized_after_verifier_gate=True, proof_commit_authorized_after_actual_both_modes=True,
    support_and_seal_after_final_review=True, local_publication_authorized_after_final_review_and_seal=True,
    no_future_execution_outcome_claimed=True, goal_status='ACTIVE_INCOMPLETE'))
print('Installed the reviewed ' + label + ' tools. All execution prerequisites remain.')
