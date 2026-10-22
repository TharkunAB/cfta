import ast
import difflib
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / '20261022-same-symbol-edge-comparison'
for name in ['run-proof-evidence.py', 'finalize-review-packet.py']:
    before = (OLD / name).read_text()
    after = before
    if name == 'finalize-review-packet.py':
        after = after.replace('84279', '85212').replace('3629', '3630').replace('728-line', '820-line')
        after = after.replace('The original 112-line candidate passes strict1, sole FULL1 and Audit1 unchanged.',
            'The selected prechecked 189-line source passes strict1, sole FULL1 and Audit1 without further edits.')
        after = after.replace("    'post_call_room_claimed': False, 'physical_language_iff_claimed': False,",
            "    'same_initial_domain_history_retained': True,\n"
            "    'next_current_room_derivable_from_initial_reservation': True,\n"
            "    'physical_language_iff_claimed': False, 'scan_completion_claimed': False,")
        after = after.replace('The SAME source/model and genuine current cache and Room premises remain explicit.\n'
            'No native Receipt on hits, future success, post-Room or physical language iff is claimed.',
            'The SAME source/model and genuine current cache premises remain explicit.\n'
            'One initial domain cache, its actual global history and one initial reservation remain fixed.\n'
            'The theorem derives current Room and the final SAME global domain history.\n'
            'The next current Room follows from this history and the unchanged initial reservation.\n'
            'No native Receipt on hits, future success or physical language iff is claimed.')
        after = after.replace('The next finite-scan capacity investigation is source-only. It has no checked body.\n'
            'It examines one initial domain cache and actual allocation history across comparisons.',
            'The next original-row stateful scan inventory and review are source-only.\n'
            'They preserve the actual comparison order, candidate promotion and SAME evolving packet.\n'
            'No completed scan, executable full pass or physical pruning equivalence is claimed.')
        after = after.replace('Three metadata command failures and their exact repairs remain recorded separately.',
            'One metadata archive command failure and its corrected retry remain recorded separately.\n'
            'The reserved local-name repair preceded every compiler run. Both source variants and the patch remain.')
    ast.parse(after)
    assert not (HERE / name).exists()
    (HERE / (name + '.H14-original.txt')).write_text(before)
    (HERE / (name + '.patch')).write_text(''.join(difflib.unified_diff(
        before.splitlines(True), after.splitlines(True), fromfile='H14/' + name, tofile='H15/' + name)))
    (HERE / name).write_text(after)
print('PASS: final helpers prepared; no finalization or verification ran')
