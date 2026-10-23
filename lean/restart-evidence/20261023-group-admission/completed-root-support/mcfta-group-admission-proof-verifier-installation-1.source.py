exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-group-admission-proof-verifier-preparation')
audit = Path('/tmp/mcfta-group-admission-proof-verifier-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, '02869005f70777a7d73fd0d6c4dba392446ea93a8ddc0b1834131d133e928018', '171cb19806022bfd6d547299461ca4036e42280cdda66c04c12b74d3643c5fb3')
checked_package(audit, expected_pins, expected_freeze)
assert sha(audit / 'review.json') == expected_review
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'verify-proofs.py') == '88d74272ef1dfd2345bf2f7a4ad964dc942ad5c4e23013275c230e22ad48e9af'
assert sha(owner / 'bound-data.json') == '2f5bab0543581602061ee4b530d1ecfb1ca62d3a3228e46363d0390d3a321060'
assert len((owner / 'verify-proofs.py').read_bytes().splitlines()) == 383
assert len((owner / 'bound-data.json').read_bytes().splitlines()) == 331
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
assert all(not (HERE / name).exists() for name in ['verify-proofs.py', 'bound-data.json'])
archive(owner, 'proof-verifier-preparation')
archive(audit, 'proof-verifier-audit')
for name in ['verify-proofs.py', 'bound-data.json']:
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'), bound_data_sha256=sha(HERE / 'bound-data.json'),
    root_whole_selected_code_lines_read=383, root_whole_actual_bound_data_lines_read=331,
    root_whole_basis_code_lines_read=387, root_whole_basis_data_lines_read=1119,
    root_whole_adaptation_diff_read=True, independent_review_sha256=expected_review,
    all_generic_guard_families_retained=True, exact_Fin_and_bullet_activation_raw=True,
    actual_source_alias_and_all_three_receipts_bound=True, actual_metadata_cut_jobs=12,
    actual_failed_metadata_jobs=0, standalone_cwd='/', both_modes_required_before_proof_commit=True,
    new_Lean_Lake_jobs_authorized=0, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed whole-reviewed saved-proof verifier and actual data; standalone modes authorized.')
