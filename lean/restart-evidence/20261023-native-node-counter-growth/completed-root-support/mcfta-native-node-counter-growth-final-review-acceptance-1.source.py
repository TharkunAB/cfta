exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
audit = Path('/tmp/mcfta-native-node-counter-growth-final-doc-audit')
checked_package(audit, expected_pins, expected_freeze)
assert sha(audit / 'review.json') == expected_review and load(audit / 'review.json')['status'] == 'CLEAR'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert proof == 'a0a671b5c3cfd7a000a5298f74603c05a48f1702'
assert git('rev-parse', 'HEAD').strip() == proof and git('rev-parse', proof + '^').strip() == START
assert git('branch', '--show-current').strip() == 'formalize'
verified, preserved = [load(HERE / name) for name in ['verification.json', 'preservation-final.json']]
assert verified['status'] == preserved['status'] == 'PASS'
assert verified['actual_jobs'] == 3 and verified['failed_jobs'] == verified['warned_source_exit_zero_jobs'] == 0
assert verified['audit_build_jobs'] == 3654 and verified['audit_dependencies'] == 75556
assert preserved['baseline_files'] == 118574 and preserved['frozen_entries'] == 1415
assert preserved['frozen_registry_count'] == 319
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
assert preserved['haskell_fix_registry_first_and_retained']
correction = load(HERE / 'closing-install-correction.json')
assert correction['status'] == 'EXACT_ARCHIVED_BASIS_PATH_CORRECTION_ONLY'
assert correction['historical_metadata_cut_unchanged'] and correction['same_verify_seal_byte_identity_guard']
archive(audit, 'final-doc-audit')
save('publication-gate.json', dict(status='ROOT_ACCEPTED', proof_commit=proof,
    publication_scope='LOCAL_ONLY', network_publication='AUTHORIZED_PENDING_ROOT_PUSH',
    independent_review_sha256=expected_review,
    root_complete_current_update_focused_note_next_target_and_repair_index_read=True,
    root_actual_progress_addendum_and_exact_metadata_correction_read=True,
    root_all_old_text_inverse_and_baseline_preservation_checked=True,
    historical_cut_and_later_closing_receipts_retained_separately=True,
    all_actual_proof_and_metadata_evidence_retained=True, postcut_metadata_failure_retained=True,
    no_haskell_repair=True, whole_goal_complete=False,
    next_actions='Archive support once. Seal with mandatory checkpoint replay at the final component count. Verify and publish locally. Then push the exact two commits to origin/formalize under standing explicit authorization.'))
print('Accepted final documentation and preservation review. Support, seal, local publication and authorized push follow in order.')
