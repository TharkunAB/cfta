from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess

work = Path(__file__).parent
old = Path('lean/restart-evidence/20261115-native-producer-origins-and-closed-reset-checkpoint-work')
base = '6e467466aec2919af58c2c904660e05bd7af36d1'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip() == base
specs = [
    ('20261115-current-edge-compile-dispatch-origin-draft', 'SourceCurrentAllocatedNativeEdgeCompileDispatchOrigin',
     'f1b5072b7f66612d5849b990a2e862e96208c3789165f038e36fd08c1056e9fe',
     ['checked_edge_body_origin_from_initial_query_finish', 'returned_edge_cell_checked_body_prefix']),
    ('20261115-current-ordinary-node-profile-isolated-list-induction-repair', 'SourceCurrentAllocatedNativeOrdinaryNodeProfile',
     '7dcf8adffc94dc6de918836d96d9fad810938f4ae2fa59ea50e9382763588293', ['ordinary_node_profile_trace_result']),
    ('20261115-original-m-reference-node-profile-bound-repair', 'SourceCurrentAllocatedNativeMixedReferenceNodeProfile',
     '481ad716e298ec1b41023b84611143bed82d0b0f9180049f6b558dda086e6e48',
     ['current_stored_universe_reference_node_profile_of_fuel_induction']),
]
promotion = []
for folder, module, digest, statements in specs:
    raw = Path('lean/restart-evidence') / folder / (module + '.lean')
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    public = Path('lean/MicroCFTA') / raw.name
    assert not public.exists()
    shutil.copyfile(raw, public)
    promotion.append({'module': module, 'raw': str(raw), 'sha256': digest, 'public_statements': statements})
status = {
    'at': datetime.datetime.now().astimezone().isoformat(), 'base': base, 'goal_active': True,
    'new_modules': 3, 'new_statements': 4, 'private_batch': {'session': 9841, 'exit': 0, 'standard_reports': 4},
    'public_gates_pending': True, 'general_native_C_M_history_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False, 'root_sole_compiler': True,
    'next_tasks': ['Actual-prefix-scoped dual Returned induction', 'Original-M row-child admission', 'Closed union producer'],
}
for name, value in [('promotion.json', promotion), ('WIP.json', status)]:
    (work / name).write_text(json.dumps(value, indent=2) + '\n')
for name in ['prepare-private.py', 'visibility-exports.json', 'modified-public.json', 'independent-examples.json', 'EndpointWarmProbes.lean.txt']:
    shutil.copyfile(old / name, work / name)
driver = (old / 'prepare-public.py').read_text()
driver = driver.replace('20261115-native-producer-origins-and-closed-reset-publication',
                        '20261115-native-edge-producers-and-mixed-cases-publication')
driver = driver.replace('expected = 359 + len(references)', 'expected = 365 + len(references)')
needle = "driver += 'report = ' + repr(report)"
assert needle in driver
driver = driver.replace(needle, "report.update({'actual_returned_edge_checked_body_origin_proved':True,'general_ordinary_node_profile_producer_proved':True,'original_m_reference_node_profile_producer_proved':True})\n" + needle)
(work / 'prepare-public.py').write_text(driver)
print(json.dumps({'promoted_exact_modules': len(promotion), 'new_statements': 4}))
