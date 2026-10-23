exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-group-admission-closing-preparation')
audit = Path('/tmp/mcfta-group-admission-closing-audit')
checked_package(owner, '54538e208c6039eff69e12bbfc999b4efb6d03594df414ebb17c49f366edcf73', '6ed3bcb306b23913d9670e210c8820731044569bf52db13d2c3f56b7c9459253')
checked_package(audit, '025e4444b61a486294cc2b3e6bb92f4afa34978665740b34d4a26e59b7656e81', 'b7c150aedbff44613c2f1ccbf1f7ee9b6cff41683ca09cff8dc02b068e2cb1b1')
assert sha(audit / 'review.json') == '51bee7c9dd17be5ce67bd90f6407acc803ba44f8650076261db36954ff285a27'
assert load(audit / 'review.json')['status'] == 'CLEAR'
names = ['verify-preservation.py', 'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'verify-checkpoint.py']
assert sum(len((owner / 'selected' / name).read_bytes().splitlines()) for name in names) == 236
assert load(HERE / 'root-closing-tool-scope-gate.json')['whole_selected_tool_hard_stop'] == 260
assert (owner / 'selected/verify-seal.py').read_bytes() == (owner / 'basis/verify-seal.py').read_bytes()
assert all(not (HERE / name).exists() for name in names)
archive(owner, 'closing-preparation')
archive(audit, 'closing-audit')
for name in names:
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
save('root-closing-tools-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FIVE_CLOSING_TOOLS',
    installed_tools={name:sha(HERE / name) for name in names}, root_whole_selected_lines_read=236,
    root_whole_basis_lines_read=240, exact_forward_and_inverse_patches_reviewed=True,
    independent_review_sha256=sha(audit / 'review.json'), no_guard_removed=True,
    support_collection_once=True, mandatory_seal_checkpoint_rerun=True,
    standalone_modes_before_proof_commit=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed all five whole-reviewed closing programs.')
