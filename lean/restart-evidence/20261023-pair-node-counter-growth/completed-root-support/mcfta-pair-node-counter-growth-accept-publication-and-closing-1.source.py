exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast
groups = [
    ('publication-preparation','publication-tool-review','publication-audit',
     '9c94a9e2a9d01bdcc28efbf10b41ca3f379c56b92a3ae48ced3dd67ac2c4acd6',
     '91ea18c4157c65de0cb6ce013f45b5324029af9a62de34440f59f36cc3c9b69c',
     'fc8fc6f4059ee775df2d79494aa48a61a69f2d1983ab79b853ec0d94f6791dae',
     'e14dab854c7fb6f88bb86742a8f9b658f2a144bac0378ee61031ac0fe0b92158',
     '26b6cf487428e2d6a32e7b9ad8f8b9f11587aa306eaedbd648dab87821476e9e',
     'root-publication-tools-review.json','ACCEPTED_COMPLETE_THREE_LOCAL_PUBLICATION_TOOLS',101,44),
    ('closing-actual-binding','closing-actual-review','closing-actual-audit',
     '8c0abb1a13c7249e71d7f3763154bb67c820b51322b386103eedeb44f5ba1f1a',
     '76d92c27c6947d71b91e9e8e41b7a429e8b02093da61d0a4dddb13d879b7b519',
     '9852fbc791d4d24091e1ba5ba953447ba2624e2759fd23ecf984fb75624e75e8',
     '7744ffd93e959002188fdf74273053f8fb1baeaf756d2ef5ee51de511449b325',
     'b5a5cfc3fc4eefaf9eda636708256dc647bce86e01bdb23aad9aaa3283d17b6b',
     'root-closing-tools-review.json','ACCEPTED_COMPLETE_FIVE_CLOSING_TOOLS',236,59)]
for owner_name,peer_name,archive_name,op,of,pp,pf,review_sha,gate_name,status,lines,assertions in groups:
    owner = Path('/tmp/mcfta-pair-node-counter-growth-' + owner_name)
    peer = Path('/tmp/mcfta-pair-node-counter-growth-' + peer_name)
    checked_package(owner,op,of)
    checked_package(peer,pp,pf)
    assert sha(peer / 'review.json') == review_sha
    review = load(peer / 'review.json')
    assert review['status'] == 'CLEAR' and review['owner_pins_sha256'] == op
    scripts = load(owner / 'selected-scripts.json')
    installed = {}
    actual_lines = actual_assertions = 0
    for name,pin in scripts.items():
        source = owner / 'selected' / name
        expected = pin.get('selected',pin)['sha256']
        assert sha(source) == expected and not (HERE / name).exists()
        actual_lines += len(source.read_bytes().splitlines())
        actual_assertions += sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(source.read_bytes())))
        installed[name] = expected
    assert actual_lines == lines and actual_assertions == assertions
    archive(owner,owner_name)
    archive(peer,archive_name)
    for name in scripts:
        (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
    save(gate_name,dict(status=status,independent_review_sha256=review_sha,
        root_complete_selected_and_basis_lines_read=lines,assertions=assertions,
        root_whole_forward_diffs_and_actual_data_binding_read=True,
        all_generic_AST_structure_and_guards_retained=True,no_new_guard_exception=True,
        installed=installed,mandatory_checkpoint_before_seal=True,support_collection_once=True,
        support_self_exclusion='mcfta-pair-node-counter-growth-support-1',
        dual_saved_modes_before_proof_commit_and_documents=True,exact_two_file_proof_commit=True,
        local_publisher_network_free=True,full_blob_mode_and_sealed_index_checks_retained=True,
        standalone_authorized_after_verifier_gate=True,proof_commit_authorized_after_actual_both_modes=True,
        support_and_seal_after_final_review=True,local_publication_authorized_after_final_review_and_seal=True,
        no_future_execution_outcome_claimed=True,goal_status='ACTIVE_INCOMPLETE'))
print('Accepted and installed the three publication programs and five actual closing programs.')
