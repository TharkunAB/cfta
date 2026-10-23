exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-rebuild-admission-closing-preparation')
review = Path('/tmp/mcfta-rebuild-admission-closing-source-audit')
checked_package(owner, '91aa448cb6f697ab1bb2cf9dfb532536e2b42ccdd4fa51cc420ca8b0a5f29610', 'fb77d0ce53127fea2c5127f2ec11cbb782fc0dd5c23dab7ab4c506f9ad710ad8')
checked_package(review, 'fd34d1ab28890156c09b1b9f5cb91073c04edc854917cdceed293901fea163b6', 'bef5930e4c54afd98bc0ecfc297e7a97d86db2a9033584d2bf75f163afb87b37')
assert sha(review / 'review.json') == '2b25a784885803c7bbbdeb3a2291141fe032d213f04b7ab151977f9c4a9a4b84'
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'closing-preparation')
archive(review, 'closing-source-audit')
installed = {}
for name in ['verify-preservation.py', 'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'verify-checkpoint.py']:
    assert not (HERE / name).exists()
    (HERE / name).write_bytes((owner / name).read_bytes())
    installed[name] = sha(HERE / name)
save('root-closing-tools-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FIVE_CLOSING_TOOLS',
    installed_tools=installed, root_whole_selected_lines_read=236, root_whole_basis_lines_read=236,
    exact_forward_and_inverse_patches_reviewed=True, independent_review_sha256=sha(review / 'review.json'),
    no_guard_removed=True, support_collection_once=True, mandatory_seal_checkpoint_rerun=True,
    standalone_modes_before_proof_commit=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed all five closing tools after complete root and independent review; none executed.')
