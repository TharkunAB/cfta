import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))
owner = Path('/tmp/mcfta-comparison-native-covered-final-doc-audit')
checked_package(owner, sys.argv[1], sys.argv[2])
assert load(owner / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'review.json') == sys.argv[3]
assert load(HERE / 'verification.json')['status'] == 'PASS'
assert load(HERE / 'preservation-final.json')['status'] == 'PASS'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof
assert git('rev-parse', 'HEAD~1').strip() == START
assert len(proof) == 40 and all(value in '0123456789abcdef' for value in proof)
archive(owner, 'final-doc-audit')
save('publication-gate.json', dict(status='ROOT_ACCEPTED', proof_commit=proof,
    publication_scope='LOCAL_ONLY', network_publication='AUTHORIZED_PENDING_ROOT_PUSH',
    independent_review_sha256=sha(owner / 'review.json'),
    root_complete_current_update_focused_note_next_target_and_repair_index_read=True,
    root_all_old_text_inverse_and_baseline_preservation_checked=True,
    no_haskell_repair=True, whole_goal_complete=False,
    next_actions='Archive support once. Seal and verify locally. Then root pushes the exact two commits to origin/formalize under standing user authorization.'))
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Publication gate\n\n')
    output.write('The final document and preservation review is CLEAR.\n')
    output.write('The local publication gate is accepted for the actual proof commit.\n')
    output.write('Support collection, seal, local publication and authorized root push remain future work at this cut.\n')
    output.write('The whole goal remains ACTIVE and incomplete.\n')
print(json.dumps(dict(status='PASS', proof_commit=proof, publication='AUTHORIZED_PENDING_ROOT_PUSH')))
