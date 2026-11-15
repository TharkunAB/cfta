from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess

base = Path('lean/restart-evidence/20261115-native-two-order-query-history-checkpoint-work')
work = Path(__file__).parent
module = 'SourceCurrentAllocatedNativeBodyFirstOuterQueryGlobalLaws'
raw = Path('lean/restart-evidence/20261115-body-first-outer-query-qualified-control-repair') / (module + '.lean')
data = raw.read_bytes()
assert hashlib.sha256(data).hexdigest() == 'dff89e741b6555db89b27a2304bdd1bd8c54575c04ef9d8cd8b418a33802589b'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip() == 'c0b99c6691c4c5a8bbaa624a5b4c4d6c238db885'
public = Path('lean/MicroCFTA') / raw.name
assert not public.exists()
promotion = [{'module': module, 'raw': str(raw), 'sha256': hashlib.sha256(data).hexdigest(),
              'public_statements': ['to_body_first_key_node_result', 'query_returned_and_raw_results',
                                    'initial_node_query_returned_and_raw_results',
                                    'initial_edge_query_returned_and_raw_results']}]
(work / 'promotion.json').write_text(json.dumps(promotion, indent=2) + '\n')
(work / 'visibility-exports.json').write_text('[]\n')
(work / 'modified-public.json').write_text('[]\n')
(work / 'independent-examples.json').write_text(json.dumps({'imports': [], 'examples': [], 'named_axiom_reports': 0}, indent=2) + '\n')
(work / 'EndpointWarmProbes.lean.txt').write_text('')
driver = (base / 'prepare-public.py').read_text()
driver = driver.replace('20261115-native-two-order-query-history-publication', '20261115-native-body-first-outer-history-publication')
driver = driver.replace('assert len(promotion) >= 2', 'assert len(promotion) >= 1')
driver = driver.replace('expected = 347 + len(references)', 'expected = 355 + len(references)')
driver = driver.replace("'global_body_first_outer_query_history_proved':False", "'global_body_first_outer_query_history_proved':True")
(work / 'prepare-public.py').write_text(driver)
shutil.copyfile(base / 'prepare-private.py', work / 'prepare-private.py')
status = {'at': datetime.datetime.now().astimezone().isoformat(),
          'base': 'c0b99c6691c4c5a8bbaa624a5b4c4d6c238db885', 'goal_active': True,
          'new_modules': 1, 'new_statements': 4,
          'private_check': {'session': 16705, 'exit': 0, 'standard_reports': 4},
          'public_gates_pending': True, 'general_native_C_M_history_proved': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False,
          'root_sole_compiler': True,
          'earlier_shell_assembly_failed_before_source_changes': True}
(work / 'WIP.json').write_text(json.dumps(status, indent=2) + '\n')
shutil.copyfile(raw, public)
assert public.read_bytes() == data
print(json.dumps({'module': module, 'raw_exact': True, 'work': str(work)}))
