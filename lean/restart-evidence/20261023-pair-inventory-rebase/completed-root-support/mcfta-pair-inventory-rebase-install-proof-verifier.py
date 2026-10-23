exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-pair-inventory-rebase-proof-verifier-preparation')
review = Path('/tmp/mcfta-pair-inventory-rebase-proof-verifier-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, '00275341204f892217fccf6eae217b14d607f853fb659c0717e058371af55b75', '28a10234ead5585e59b865018bbfedd0d9b199bc109560272e57bc1a86b82d33')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'proof-verifier-preparation')
archive(review, 'proof-verifier-audit')
for name, expected in [('verify-proofs.py', '8457f207929ea37985139ac13efe98ba1f09857d4a56d1f9ac7eefa7624f32d7'),
        ('bound-data.json', '4b5abbcae64b1ddac1a0965424e1df8672280c2ca377672a9f00b73e9c3b88a6')]:
    assert not (HERE / name).exists() and sha(owner / name) == expected
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'), bound_data_sha256=sha(HERE / 'bound-data.json'),
    root_whole_selected_code_lines_read=384, root_whole_actual_bound_data_lines_read=282,
    root_whole_basis_code_lines_read=382, root_whole_basis_data_lines_read=277,
    root_whole_adaptation_diff_read=True, independent_review_sha256=expected_review,
    all_generic_guard_families_retained=True, six_fragment_metadata_and_all_local_binder_guards=True,
    soft_target_deviation_lines=2, deviation_reason='Required included-proof intro scope and exact canonical lambda binder checks.',
    whole_selected_source_hard_stop=400, actual_metadata_cut_jobs=14, actual_failed_metadata_jobs=0,
    standalone_cwd='/', both_modes_required_before_proof_commit=True,
    new_Lean_Lake_jobs_authorized=0, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed complete source-reviewed verifier and actual table. Both saved modes are authorized.')
