from pathlib import Path
import datetime
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
base = 'ca5a4bcbd0ea06e92d332f50c16190aaa97be4d1'
read = lambda *args: subprocess.check_output(['git', *args], cwd=root).decode().strip()
assert read('rev-parse', 'HEAD') == base
assert read('branch', '--show-current') == 'formalize'
assert not read('diff', '--cached', '--name-only')
assert not read('diff', '--name-only', '--', 'lean/MicroCFTA')
prior = root / 'lean/restart-evidence/20261116-real-prefix-all-outcome-checkpoint'
old_pins = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
run = root / 'lean/restart-evidence/20261116-native-callback-and-isolation-repairs-check'
checked = next(item for item in json.loads((run / 'checks.json').read_text()) if item['name'] == 'real-callback')
assert checked['exit'] == 0 and checked['total_axiom_reports'] == 2 and not checked['nonstandard_axioms']
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
raw = root / 'lean/restart-evidence/20261116-current-real-worker-callback-raw-membership-repair/SourcePruningEnumerationRealWorkerCallbackResources.lean'
assert hashlib.sha256(raw.read_bytes()).hexdigest() == 'd1568491925808a952c69b4ff7826e624da3b0f65647f4f4bf6281874fb28a35'
target = root / 'lean/MicroCFTA' / raw.name
assert not target.exists()
audit = root / 'lean/MicroCFTA/Audit.lean'
(work / 'BASE-AUDIT.lean.txt').write_bytes(audit.read_bytes())
target.write_bytes(raw.read_bytes())
probes = ''
for law in ['recorded_callback_current_at_original_budget', 'real_callback_resources_of_depth_induction']:
    qualified = 'MicroCFTA.SourcePruningEnumerationRealWorkerCallbackResources.' + law
    probes += '\n#check @' + qualified + '\n#print axioms ' + qualified + '\n'
audit.write_bytes(b'import MicroCFTA.SourcePruningEnumerationRealWorkerCallbackResources\n' + audit.read_bytes() + probes.encode())
subprocess.run(['git', 'add', '--', str(target.relative_to(root)), 'lean/MicroCFTA/Audit.lean'], cwd=root, check=True)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Prove actual recursive callback resources at the supplied budget'], cwd=root, check=True)
(work / 'callback-promotion.json').write_text(json.dumps({'at':datetime.datetime.now().astimezone().isoformat(),
    'base':base,'code':read('rev-parse','HEAD'),'new_public_theorems':2,'strict_callback_reports':2,
    'private_run_overall_exit':1,'independent_callback_exit':0,'source_files':6123,
    'whole_real_worker_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False},indent=2)+'\n')
print(read('rev-parse','HEAD'))
