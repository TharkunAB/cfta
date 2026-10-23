exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import ast, sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
owner = Path('/tmp/mcfta-stored-node-counter-growth-closing-source')
peer = Path('/tmp/mcfta-stored-node-counter-growth-closing-tool-audit')
checked_package(owner, 'f6342787d7ba7744462b1795987c2ec749cdce06cdf7fabf611f8fcff410ef4f', '9c1ca14142d39f8d7e38dcc9a545201c5d0cd830d76a0e094010ebca2d7fb9fe')
checked_package(peer, expected_pins, expected_freeze)
assert sha(peer / 'review.json') == expected_review and load(peer / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'root-closing-scope-gate.json')['selected_authorship_authorized']
names = ['verify-preservation.py', 'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'verify-checkpoint.py']
assert sum(len((owner / 'selected' / name).read_bytes().splitlines()) for name in names) == 236
assert sum(isinstance(node, ast.Assert) for name in names for node in ast.walk(ast.parse((owner / 'selected' / name).read_bytes()))) == 59
assert (owner / 'selected/verify-seal.py').read_bytes() == (owner / 'basis/verify-seal.py').read_bytes()
archive(owner, 'closing-preparation')
archive(peer, 'closing-tool-audit')
installed = {}
for name in names:
    assert not (HERE / name).exists()
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
    installed[name] = sha(HERE / name)
save('root-closing-tools-review.json', dict(status='ACCEPTED_COMPLETE_FIVE_CLOSING_TOOLS',
    independent_review_sha256=expected_review, root_complete_selected_and_basis_lines_read=236,
    root_whole_forward_diffs_and_actual_data_binding_read=True, assertions=59,
    all_generic_AST_structure_and_guards_retained=True, no_new_guard_exception=True,
    installed=installed, mandatory_checkpoint_before_seal=True, verify_seal_byte_identical=True,
    support_collection_once=True, support_self_exclusion='mcfta-stored-node-counter-growth-support-1',
    preservation_execution_after_verified_documents=True, support_and_seal_after_final_review=True,
    no_future_execution_outcome_claimed=True, goal_status='ACTIVE_INCOMPLETE'))
print('Installed exact five reviewed closing tools; later document and final review prerequisites remain.')
