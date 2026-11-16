from pathlib import Path
import datetime
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
base = '79155bfa2a24ad0629e97f67e08419b46a0dc248'
read = lambda *args: subprocess.check_output(['git', *args], cwd=root).decode().strip()
assert read('rev-parse', 'HEAD') == base
assert read('branch', '--show-current') == 'formalize'
assert not read('diff', '--cached', '--name-only')
assert not read('diff', '--name-only', '--', 'lean/MicroCFTA')
prior = root / 'lean/restart-evidence/20261115-real-prefix-and-opaque-resources-checkpoint'
old_pins = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
all_run = root / 'lean/restart-evidence/20261116-native-real-prefix-selection-reference-check'
current_run = root / 'lean/restart-evidence/20261116-native-real-resources-strict-normalization-check'
all_result = json.loads((all_run / 'checks.json').read_text())[-1]
current_result = json.loads((current_run / 'checks.json').read_text())[-1]
assert all_result['exit'] == current_result['exit'] == 0
assert all_result['total_axiom_reports'] == 3 and current_result['total_axiom_reports'] == 1
assert not all_result['nonstandard_axioms'] and not current_result['nonstandard_axioms']
for run in [all_run, current_run]:
    for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
audit = root / 'lean/MicroCFTA/Audit.lean'
(work / 'BASE-AUDIT.lean.txt').write_bytes(audit.read_bytes())
specs = [
    ('20261116-current-real-prefix-all-outcome-selection-reference-repair',
     'SourcePruningEnumerationRealPrefixAllResources.lean',
     'd5b38684f391f829978a1189d53ffe31b5d581be378b7c957b76a98d91c24d5a',
     ['prefix_real_resources_at_original_budget', 'prefix_zero_stops_and_not_current',
      'real_prefix_noncontinuing_emits_no_output'],
     'Prove resources for every real prefix outcome at the supplied budget'),
    ('20261116-current-real-prefix-continuing-normalization-repair',
     'SourcePruningEnumerationRealPrefixContinuingResources.lean',
     'a4aa29f351942383e910ab40a9fd172e1eee6bef3b80f3601c9a2767a0dbf9f8',
     ['prefix_real_continuing_current_at_original_budget'],
     'Prove current resources for every continuing real prefix')]
commits = []
for folder, name, digest, laws, message in specs:
    raw = root / 'lean/restart-evidence' / folder / name
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    target = root / 'lean/MicroCFTA' / name
    assert not target.exists()
    target.write_bytes(raw.read_bytes())
    probes = ''
    for law in laws:
        qualified = 'MicroCFTA.SourcePruningEnumerationSharedRecursive.' + law
        probes += '\n#check @' + qualified + '\n#print axioms ' + qualified + '\n'
    audit.write_bytes(('import MicroCFTA.' + target.stem + '\n').encode() + audit.read_bytes() + probes.encode())
    subprocess.run(['git', 'add', '--', str(target.relative_to(root)), 'lean/MicroCFTA/Audit.lean'], cwd=root, check=True)
    subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
    subprocess.run(['git', 'commit', '--quiet', '-m', message], cwd=root, check=True)
    commits.append(read('rev-parse', 'HEAD'))
data = {'at':datetime.datetime.now().astimezone().isoformat(), 'base':base,
    'code':read('rev-parse', 'HEAD'), 'commits':commits, 'new_modules':2, 'new_public_theorems':4,
    'old_non_audit_sources_byte_exact':6119, 'all_original_headers_and_budgets_unchanged':True,
    'whole_identity_worker_proved':False, 'whole_real_worker_proved':False,
    'joint_finite_completion_proved':False, 'haskell_changed':False}
(work / 'promotion.json').write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps(data))
