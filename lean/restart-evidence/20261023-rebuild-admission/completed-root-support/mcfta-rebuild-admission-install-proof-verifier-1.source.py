exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-rebuild-admission-proof-verifier-preparation')
review = Path('/tmp/mcfta-rebuild-admission-proof-verifier-audit')
checked_package(owner, 'ec13fe871a84fcff26450e1fcb55b2d31131c5419d27001c871e7f35afe0e0a4', '186b4867ed050c48e2b37a525087eccb0086ef56d639d9cde2636eb2b65b2622')
checked_package(review, 'f27304508e86a25c0c07a7effbb2fd46a1011741220080a8936413c3bbf174fa', 'e6760bec8fe01fcefb41e009f2c6158fdb638825c3208f05e0a12cd207ecb920')
assert sha(review / 'review.json') == 'cd4679da72b1e143b3b9e75a747e18e4bb099e3b9c22ccbf3fa1568b169b18f9'
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'proof-verifier-preparation')
archive(review, 'proof-verifier-audit')
for name, expected in [('verify-proofs.py', '7bd488249d18ce83368e2334047dc08421e85bcd5e16c8616be6905f68e308cd'),
        ('bound-data.json', '7887ffda3d4cdae36892fccef1bb62a33b76b590bad89c815615aee65fe59959')]:
    assert not (HERE / name).exists() and sha(owner / name) == expected
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'), bound_data_sha256=sha(HERE / 'bound-data.json'),
    root_whole_selected_code_lines_read=382, root_whole_actual_bound_data_lines_read=277,
    root_whole_basis_code_lines_read=383, root_whole_basis_data_lines_read=331,
    root_whole_adaptation_diff_read=True, independent_review_sha256=sha(review / 'review.json'),
    all_generic_guard_families_retained=True, exact_public_lets_and_introduced_fields=True,
    actual_metadata_cut_jobs=13, actual_failed_metadata_jobs=0,
    later_closing_metadata_failure_retained_separately=True,
    standalone_cwd='/', both_modes_required_before_proof_commit=True,
    new_Lean_Lake_jobs_authorized=0, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed complete source-reviewed verifier and bound data; both saved modes are now authorized.')
