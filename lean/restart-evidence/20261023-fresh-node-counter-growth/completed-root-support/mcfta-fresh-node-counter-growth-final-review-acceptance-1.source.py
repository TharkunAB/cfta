exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import sys
expected_proof, expected_pins, expected_freeze, expected_review = sys.argv[1:]
audit = Path('/tmp/mcfta-fresh-node-counter-growth-final-doc-audit')
checked_package(audit, expected_pins, expected_freeze)
assert sha(audit / 'review.json') == expected_review
assert load(audit / 'review.json')['status'] == 'CLEAR'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert proof == expected_proof and len(proof) == 40
assert git('rev-parse', 'HEAD').strip() == proof
assert git('rev-parse', proof + '^').strip() == START
assert git('branch', '--show-current').strip() == 'formalize'
verified, preserved = [load(HERE / name) for name in ['verification.json', 'preservation-final.json']]
assert verified['status'] == preserved['status'] == 'PASS'
assert verified['actual_jobs'] == 5 and verified['failed_jobs'] == 1
assert verified['warned_source_exit_zero_jobs'] == 1
assert verified['audit_build_jobs'] == 3652 and verified['audit_dependencies'] == 75541
assert preserved['baseline_files'] == 113643 and preserved['frozen_entries'] == 1413
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
assert preserved['haskell_fix_registry_first_and_retained']
archive(audit, 'final-doc-audit')
save('publication-gate.json', dict(status='ROOT_ACCEPTED', proof_commit=proof,
    publication_scope='LOCAL_ONLY', network_publication='AUTHORIZED_PENDING_ROOT_PUSH',
    independent_review_sha256=expected_review,
    root_complete_current_update_focused_note_next_target_and_repair_index_read=True,
    root_actual_progress_addendum_read=True,
    root_all_old_text_inverse_and_baseline_preservation_checked=True,
    historical_cut_and_later_closing_receipts_retained_separately=True,
    all_failed_warned_proof_and_failed_metadata_evidence_retained=True,
    no_haskell_repair=True, whole_goal_complete=False,
    next_actions='Archive support once. Seal with mandatory checkpoint replay. Verify and publish locally. Then push the exact two commits to origin/formalize under standing explicit authorization.'))
print('ACCEPTED final documentation and actual preservation review; support/seal/local publication/root push authorized in order.')
