import ast
import datetime
import difflib
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

source = Path('/tmp/mcfta-completed-hit-readback-checkpoint-preparation')
audit = Path('/tmp/mcfta-completed-hit-readback-checkpoint-preparation-audit')
pins = checked_package(source, '7101e1cb10465525e7040dbf7a8878c2fc3eb99a611a972d4409ec2b1e573c1f',
    '8942ca111e869bbc898738ccf6b96bbd57e9b4be64df51c1f4fb68efaa260ffc')
assert len(pins) == 97
selected = load(source / 'selected-scripts.json')['scripts']
assert len(selected) == 12
total_lines = assertions = 0
tokens = set()
for name, pin in selected.items():
    path = source / name
    data = path.read_bytes()
    assert sha(path) == pin['sha256'] and len(data) == pin['bytes']
    assert len(data.splitlines()) == pin['lines']
    count = sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(data)))
    assert count == pin['ast_assertions']
    total_lines += pin['lines']
    assertions += count
    tokens.update(re.findall(r'__H27_[A-Z0-9_]+__', data.decode()))
    predecessor = source / pin['predecessor']
    assert predecessor.read_bytes() == (ROOT / 'lean/restart-evidence/20261023-both-miss-native-covered' / name).read_bytes()
    for field, first, second in [('diff', predecessor.read_text(), data.decode()),
            ('inverse_diff', data.decode(), predecessor.read_text())]:
        patch = (source / pin[field]).read_text()
        if first == second:
            assert patch == ''
        else:
            assert patch.startswith('--- ') and '\n+++ ' in patch
            diff_lines = patch.splitlines(True)
            before, after = [line[4:].rstrip('\n') for line in diff_lines[:2]]
            assert patch == ''.join(difflib.unified_diff(first.splitlines(True), second.splitlines(True),
                fromfile=before, tofile=after))
assert (total_lines, assertions, len(tokens)) == (1006, 325, 33)
stop = 'assert False, "__H27_EXACT_DECLARATION_FRAGMENT_CHECK_PENDING__"'
assert (source / 'verify-proofs.py').read_text().count(stop) == 1
assert load(source / 'pending-bindings.json')['distinct_script_tokens'] == 33
assert load(source / 'pending-bindings.json')['data_slot_count'] == 32
for name in ['check-full-public.py', 'verify-proofs.py']:
    assert '__H27_PRIVATE_NAMES_JSON__' in (source / name).read_text()
assert not (ROOT / 'lean/MicroCFTA' / (NAME + '.lean')).exists()
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
archive(source, 'checkpoint-preparation')
archive(audit, 'checkpoint-preparation-audit')
report = dict(status='ROOT_PENDING_TOOLS_REVIEW_CLEAR_WITH_EXACT_FRAGMENT_STOP',
    observed_at=datetime.datetime.now().astimezone().isoformat(), root_whole_program_read=True,
    scripts=12, lines=total_lines, static_ast_assertions=assertions,
    literal_data_slots=32, non_bindable_exact_fragment_stop=1,
    predecessor_bytes_match=True, all_forward_and_inverse_program_diffs_verified=True,
    whole_program_deltas_reviewed=True, approved_private_list_required_by_reader_and_verifier=True,
    independent_review_sha256=sha(audit / 'review.json'), exact_declaration_overlay_required=True,
    prepared_execution_authorized=False, proof_outcomes_bound=False, whole_goal_complete=False)
save('root-preparation-review.json', report)
print(json.dumps(report))
