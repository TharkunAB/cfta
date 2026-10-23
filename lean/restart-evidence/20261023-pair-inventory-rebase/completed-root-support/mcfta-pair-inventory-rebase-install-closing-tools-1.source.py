exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-pair-inventory-rebase-closing-preparation')
review = Path('/tmp/mcfta-pair-inventory-rebase-closing-source-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, '8b2024a9749e88912de92d60e81e9d8d4957777df21d9a4485d3b015ed26cb6a', 'ea4651a2158f0313507e80a2f57209c482b822f3039063c8fa88bc746c0e951a')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'closing-preparation')
archive(review, 'closing-source-audit')
installed = {}
for name in ['verify-preservation.py', 'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'verify-checkpoint.py']:
    assert not (HERE / name).exists()
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
    installed[name] = sha(HERE / name)
assert installed['verify-seal.py'] == '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7'
save('root-closing-tools-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FIVE_CLOSING_TOOLS',
    installed_tools=installed, root_whole_selected_lines_read=236, root_whole_basis_lines_read=236,
    exact_forward_and_inverse_patches_reviewed=True, independent_review_sha256=expected_review,
    no_guard_removed=True, support_collection_once=True, mandatory_seal_checkpoint_rerun=True,
    standalone_modes_before_proof_commit=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed all five closing tools after complete Root and independent review; none executed.')
