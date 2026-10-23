import ast
import datetime
import difflib
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

source = Path('/tmp/mcfta-both-miss-native-covered-checkpoint-preparation')
audit = Path('/tmp/mcfta-both-miss-native-covered-checkpoint-preparation-audit')
pins = checked_package(source,
    '2f3b05c4030a2b5796b610983196ad11bf3df5e0458b8de4b33763cd0e4ab90d',
    '73d9b0ada36e107847365f1d7d0e931685af2418e155349b540c5b6954f91478')
assert len(pins) == 77
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
    tokens.update(re.findall(r'__H26_[A-Z0-9_]+__', data.decode()))
    predecessor = source / pin['predecessor']
    assert predecessor.read_bytes() == (ROOT / 'lean/restart-evidence/20261023-pair-request-admission' / name).read_bytes()
    patch = (source / pin['diff']).read_text()
    if predecessor.read_bytes() == data:
        assert patch == ''
    else:
        assert patch.startswith('--- ') and '\n+++ ' in patch
        diff_lines = patch.splitlines(True)
        before = diff_lines[0][4:].rstrip('\n')
        after = diff_lines[1][4:].rstrip('\n')
        expected = ''.join(difflib.unified_diff(predecessor.read_text().splitlines(True),
            data.decode().splitlines(True), fromfile=before, tofile=after))
        assert patch == expected
assert (total_lines, assertions, len(tokens)) == (1007, 325, 32)
stop = 'assert False, "__H26_EXACT_DECLARATION_FRAGMENT_CHECK_PENDING__"'
assert (source / 'verify-proofs.py').read_text().count(stop) == 1
assert load(source / 'pending-bindings.json')['distinct_script_tokens'] == 32
assert not (ROOT / 'lean/MicroCFTA' / (NAME + '.lean')).exists()
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
archive(source, 'checkpoint-preparation')
archive(audit, 'checkpoint-preparation-audit')
report = dict(status='ROOT_PENDING_TOOLS_REVIEW_CLEAR_WITH_EXACT_FRAGMENT_STOP',
    observed_at=datetime.datetime.now().astimezone().isoformat(), root_whole_program_read=True,
    scripts=12, lines=total_lines, static_ast_assertions=assertions,
    literal_data_slots=31, non_bindable_exact_fragment_stop=1,
    predecessor_bytes_match=True, whole_program_deltas_reviewed=True,
    independent_review_sha256=sha(audit / 'review.json'),
    exact_declaration_overlay_required=True, prepared_execution_authorized=False,
    proof_outcomes_bound=False, whole_goal_complete=False)
save('root-preparation-review.json', report)
print(json.dumps(report))
