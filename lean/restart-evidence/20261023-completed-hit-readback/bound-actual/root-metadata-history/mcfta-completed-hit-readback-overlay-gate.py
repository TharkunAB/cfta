import ast
import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

source = Path('/tmp/mcfta-completed-hit-readback-declaration-overlay')
audit = Path('/tmp/mcfta-completed-hit-readback-declaration-overlay-audit')
assert len(checked_package(source,
    '997d7e27ce46176f364785e35f562299ce8cd9344c3f1aa4ea24521e68718dcb',
    '8b7418bd22727ea52f43c1f7b439d27d8a92f51bd33cf4b332304b40dec3de50')) == 33
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'SOURCE_ONLY_EXACT_DECLARATION_OVERLAY_CLEAR'
old = (HERE / 'checkpoint-preparation/verify-proofs.py').read_text()
selected = (source / 'verify-proofs.py').read_text()
stop = 'assert False, "__H27_EXACT_DECLARATION_FRAGMENT_CHECK_PENDING__"\n'
stop += '# Replace this non-bindable STOP only through an independently reviewed exact-declaration overlay.\n'
stop += '# No public/private/local fragment shape is accepted by this pending program.\n'
block = (source / 'replacement-block.py.txt').read_text()
assert old.count(stop) == 1 and len(block.splitlines()) == 72
assert old.replace(stop, block, 1) == selected
assert sha(source / 'verify-proofs.py') == 'fc6f2357dfe253f0b0002274fac2fd3989b58d4efbcc93eb8d9fed15c0d73fad'
assert len(selected.splitlines()) == 343
assert sum(isinstance(item, ast.Assert) for item in ast.walk(ast.parse(selected))) == 172
declaration = load(HERE / 'root-declaration-review.json')
schema = load(HERE / 'signature-plan/declaration-schema.json')
assert declaration['private_names'] == schema['private_helpers'] == ['yielded_done', 'ret_checked']
assert declaration['local_names'] == schema['all_have_names_including_inferred']
assert declaration['local_let_names'] == schema['all_let_names_including_inferred']
assert declaration['local_induction'] == schema['helper_induction']
assert declaration['contract_sha256'] == sha(HERE / 'signature-plan/contracts.json')
archive(source, 'declaration-overlay')
archive(audit, 'declaration-overlay-audit')
report = dict(status='ROOT_EXACT_DECLARATION_OVERLAY_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_read_entire_predecessor_and_changed_block=True, exact_whole_file_reconstruction=True,
    whole_selected_program_lines=343, selected_program_assertions=172,
    composite_tool_lines=1075, composite_tool_assertions=368,
    selected_verifier='declaration-overlay/verify-proofs.py',
    selected_verifier_sha256=sha(source / 'verify-proofs.py'),
    independent_review_sha256=sha(audit / 'review.json'),
    ten_literal_contracts_required=True, current_root_declaration_shape_matches=True,
    actual_metrics_bindings_pending=True, verifier_activated=False,
    prepared_execution_authorized=False, whole_goal_complete=False)
save('root-declaration-overlay-review.json', report)
print(json.dumps(report))
