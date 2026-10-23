import ast
import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

source = Path('/tmp/mcfta-both-miss-native-covered-declaration-overlay')
audit = Path('/tmp/mcfta-both-miss-native-covered-declaration-overlay-audit')
assert len(checked_package(source,
    'acd99a1100cf5ba113264a6d1ba201c2243e24d3f429eec82c83eea7b913e415',
    '74c051431264f78662cdbc9c52d64503206c29c6aa31ad9a7c15f137b7cfeb8b')) == 96
assert len(checked_package(audit,
    'a654a5db4c7be21ffafbc337fca905ece1d1fa52d7f85a1aa69f7f087ebcb706',
    '9cfc58a0a9e226f656dc1741dd64b0bf1222d315b5ed3b39f06b3348744fbaf2')) == 101
assert sha(audit / 'review.json') == '69305c8a31d159b768701785a59aa5989d60a3486271d6453a92e98ac6039cca'
assert load(audit / 'review.json')['status'] == 'SOURCE_ONLY_CHECKER_OVERLAY_CLEAR'
old = (HERE / 'checkpoint-preparation/verify-proofs.py').read_text()
selected = (source / 'verify-proofs.py').read_text()
stop = 'assert False, "__H26_EXACT_DECLARATION_FRAGMENT_CHECK_PENDING__"\n'
stop += '# Replace this rejecting block only after separate exact declaration review.\n'
stop += '# The reviewed overlay must check every compiled fragment and its source order.\n'
block = (source / 'exact-declaration-checker.block.txt').read_text()
assert old.count(stop) == 1 and len(block.splitlines()) == 43
assert old.replace(stop, block, 1) == selected
assert sha(source / 'verify-proofs.py') == 'b7dbf05d15499601f78950d5b02e53add0a7b440cf2c7e87d2bdfcc45707af5b'
assert len(selected.splitlines()) == 314
assert sum(isinstance(item, ast.Assert) for item in ast.walk(ast.parse(selected))) == 149
declaration = load(HERE / 'root-declaration-review.json')
required = load(source / 'overlay-interface.json')['root_declaration_review_required_shape']
for key, value in required.items():
    if key != 'contracts':
        assert declaration[key] == value, key
assert declaration['contract_sha256'] == sha(HERE / 'signature-plan/contracts.json')
archive(source, 'declaration-overlay')
archive(audit, 'declaration-overlay-audit')
report = dict(status='ROOT_EXACT_DECLARATION_OVERLAY_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_read_entire_predecessor_and_changed_block=True, exact_whole_file_reconstruction=True,
    whole_selected_program_lines=314, selected_program_assertions=149,
    composite_tool_lines=1047, composite_tool_assertions=345,
    selected_verifier='declaration-overlay/verify-proofs.py',
    selected_verifier_sha256=sha(source / 'verify-proofs.py'),
    independent_review_sha256=sha(audit / 'review.json'),
    ten_literal_contracts_required=True, current_root_declaration_shape_matches=True,
    actual_metrics_bindings_pending=True, verifier_activated=False,
    prepared_execution_authorized=False, whole_goal_complete=False)
save('root-declaration-overlay-review.json', report)
print(json.dumps(report))
