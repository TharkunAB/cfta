exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
audit = Path('/tmp/mcfta-cluster-admission-final-doc-audit')
expected_pins, expected_frozen, expected_review = sys.argv[1:]
assert all(len(value) == 64 and set(value) <= set('0123456789abcdef') for value in sys.argv[1:])
checked_package(audit, expected_pins, expected_frozen)
assert sha(audit / 'review.json') == expected_review
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'verification.json')['status'] == 'PASS'
preserved = load(HERE / 'preservation-final.json')
assert preserved['status'] == 'PASS' and preserved['baseline_files'] == 107353
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
assert preserved['frozen_registry_count'] == 313 and preserved['frozen_entries'] == 1407
assert preserved['unchanged_older_non_audit_sources'] == 3644
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof
assert git('rev-parse', proof + '^').strip() == START
assert load(HERE / 'root-proof-verifier-v2-review.json')['mathematical_sources_unchanged']
assert not (HERE / 'completed-root-support').exists()
assert not (HERE / 'SHA256SUMS').exists()
archive(audit, 'final-doc-audit')
save('publication-gate.json', dict(
    status='ROOT_ACCEPTED', proof_commit=proof, publication_scope='LOCAL_ONLY',
    network_publication='AUTHORIZED_PENDING_ROOT_PUSH', independent_review_sha256=expected_review,
    root_complete_current_update_focused_note_next_target_and_repair_index_read=True,
    root_all_old_text_inverse_and_baseline_preservation_checked=True,
    no_haskell_repair=True, whole_goal_complete=False,
    next_actions='Archive support once. Seal with mandatory checkpoint replay. Verify and publish locally. Then push the exact two commits to origin/formalize under standing explicit authorization.'))
print('ACCEPTED final documents and preservation; support collection and seal may proceed.')
