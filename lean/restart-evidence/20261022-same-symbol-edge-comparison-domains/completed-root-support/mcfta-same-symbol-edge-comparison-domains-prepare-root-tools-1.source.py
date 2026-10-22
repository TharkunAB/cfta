import ast
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / '20261022-same-symbol-edge-comparison'
SOURCE = '8ae94566570cf99ec3eb61ec991d36a1df196c5b9c2bc2fca4aeb88fd6305e15'
names = ['accept-full-review.py', 'install-source.py', 'bind-actual-evidence.py', 'activate-proof-tools.py']
pins = {}
for name in names:
    before = (OLD / name).read_text()
    after = before.replace('SourceCurrentSameSymbolEdgeComparison', 'SourceCurrentSameSymbolEdgeComparisonDomains')
    after = after.replace('same-symbol-edge-comparison-', 'same-symbol-edge-comparison-domains-')
    after = after.replace('02d01576ce9e7188342835138452a5163b150e28c264c01782137848e1a1c560', SOURCE)
    if name == 'accept-full-review.py':
        after = after.replace('728', '820').replace('69839', '81492').replace('727', '819')
        after = after.replace('7fb94c311d5eff9aa93faa2dab7cc235a2e9dffe365b98d2c5ca04c39c49dd8d',
                              'f5002f8fd824745fd0147abd2ef1489ef77d8bfecb6d7920e55bc0bd3bf644a7')
        after = after.replace('== 112', '== 189').replace("'source_lines': 112", "'source_lines': 189")
        after = after.replace("['private_namespace_helpers_checked'] == []",
                              "['private_namespace_helpers_checked'] == ['original_of_readback', 'rows_scope']")
        after = after.replace('[[1, 185], [186, 370], [371, 555], [556, 820]]',
                              '[[1, 210], [211, 420], [421, 630], [631, 820]]')
        after = after.replace("    'actual_source_current_readiness_and_room_premises': True,\n", '')
        after = after.replace("    'future_success_premise': False, 'post_call_room_claimed': False,",
            "    'same_initial_domain_history_and_reservation_premises': True,\n"
            "    'current_room_derived': True, 'final_global_domain_history_derived': True,\n"
            "    'next_current_room_derivable': True, 'scan_completion_claimed': False,\n"
            "    'future_success_premise': False,")
    elif name == 'install-source.py':
        after = after.replace('112', '189').replace('3119', '3120')
        after = after.replace('d80480df15a3908dd6c1589b9f6182546d7a4dc09cca9da36098f9289d91c3c6',
                              'fa6c433f47dca1a9b5433edd416e98f742592352920ecd5969494e0b977d4d37')
        after = after.replace('20261022-same-symbol-edge-original-rows', '20261022-same-symbol-edge-comparison')
        after = after.replace('install-source.H13-original', 'install-source.H14-original')
        after = after.replace("fromfile='H13-install', tofile='H14-install'", "fromfile='H14-install', tofile='H15-install'")
    elif name == 'bind-actual-evidence.py':
        after = after.replace('__H14_', '__H15_')
        after = after.replace('backup-same-symbol-edge-comparison-domains-20261022-0424',
                              'backup-same-symbol-edge-comparison-domains-20261022-0500')
        after = after.replace("    'ACTUAL_AXIOMS_JSON':", "    'AXIOMS_JSON': json.dumps(readback['heads'][0]['actual_axioms']),\n    'ACTUAL_AXIOMS_JSON':")
    else:
        after = after.replace('__H14_', '__H15_')
    ast.parse(after)
    assert before != after
    target = HERE / name
    assert not target.exists()
    (HERE / (name + '.H14-original.txt')).write_text(before)
    (HERE / (name + '.patch')).write_text(''.join(difflib.unified_diff(
        before.splitlines(True), after.splitlines(True), fromfile='H14/' + name, tofile='H15/' + name)))
    target.write_text(after)
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
(HERE / 'root-helper-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PREPARED_NOT_EXECUTED', 'helpers': pins}))
