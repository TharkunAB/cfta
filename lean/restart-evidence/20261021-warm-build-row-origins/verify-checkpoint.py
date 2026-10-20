import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(stem, source=None, empty=False):
    data = read(stem + '.json')
    assert data['exit_code'] == 0, stem
    assert read(stem + '.limits.json') == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = read(stem + '.usage.json')
    assert usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
    assert data['wrapper'][data['wrapper'].index('--mem') + 1] == '4G'
    assert data['wrapper'][data['wrapper'].index('--time') + 1] == '5m'
    if source:
        assert data['sha256'] == sha(ROOT / source) == sha(HERE / data['source'])
    if empty:
        assert not (HERE / (stem + '.log')).read_bytes(), stem
    return data


sources = read('selected-sources.json')
for source, entry in sources.items():
    assert sha(ROOT / source) == entry['sha256']
    checked(entry['strict'], source, True)
for stem in ['root-warm-trace-canonical-1', 'root-warm-rows-canonical-3']:
    checked(stem)
    replayed = re.findall(r'^warning:.*$', (HERE / (stem + '.log')).read_text(), re.M)
    assert all('InternedFreshOrdinaryClosedCompletion.lean' in line for line in replayed), replayed
checked('root-warm-rows-audit-3')
audit = (HERE / 'root-warm-rows-audit-3.log').read_text()
assert re.findall(r'Build completed successfully \((\d+) jobs\)', audit)[-1] == '3542'
assert re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit)[-1] == '74348'
warnings = re.findall(r'^warning:.*$', audit, re.M)
assert warnings and all('InternedFreshOrdinaryClosedCompletion.lean' in line for line in warnings), warnings
for folder, verifier, live in [
    ('warm-trace', 'warm-publication-trace-verify.py', True),
    ('warm-rows', 'warm-row-verify.py', False),
    ('warm-prefix', 'warm-prefix-verify.py', True),
    ('warm-fixture', 'warm-row-kernels-verify.py', True),
]:
    command = ['/usr/bin/python3', str(HERE / folder / verifier)]
    if live:
        command.append('--live')
    subprocess.run(command, check=True, stdout=subprocess.DEVNULL, cwd='/')
fixture = read('selected-fixture.json')
checked(fixture['strict'])
assert read(fixture['strict'] + '.json')['sha256'] == sha(HERE / fixture['source'])
assert not (HERE / (fixture['strict'] + '.log')).read_bytes()
preservation = subprocess.check_output(['/usr/bin/python3', str(HERE / 'verify-preservation.py')], text=True)
preserved = json.loads(preservation)
assert preserved['status'] == 'PASS'
(HERE / 'preservation-final.json').write_text(json.dumps(preserved, indent=2) + '\n')
unique = {}
for path in HERE.rglob('*.json'):
    try:
        entry = json.loads(path.read_text())
    except ValueError:
        continue
    if (isinstance(entry, dict) and isinstance(entry.get('command'), list)
            and entry['command'] and Path(entry['command'][0]).name in ['lean', 'lake']
            and 'wrapper' in entry and isinstance(entry.get('exit_code'), int)):
        unique.setdefault(json.dumps(entry, sort_keys=True), []).append(str(path.relative_to(HERE)))
launch = read('warm-trace/warm-publication-trace-direct-1.json')
assert json.dumps(launch, sort_keys=True) in unique
accounting = {'actual_lean_lake_jobs': len(unique) - 1,
    'capped_command_attempt_receipts': len(unique),
    'nonzero_command_receipts': sum(json.loads(key)['exit_code'] != 0 for key in unique),
    'nonzero_lean_jobs': sum(json.loads(key)['exit_code'] != 0 for key in unique) - 1,
    'copies_add_commands': False, 'pre_lean_launch_failures': 1,
    'warning_bearing_successes_preserved': True, 'weaker_successes_preserved_unselected': True,
    'commands': [{'receipts': paths, 'exit_code': json.loads(key)['exit_code']} for key, paths in unique.items()]}
(HERE / 'attempt-accounting.json').write_text(json.dumps(accounting, indent=2) + '\n')
report = {'status': 'PASS', 'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
    'goal_status': 'active', 'new_public_theorems': 3, 'new_public_definitions': 1,
    'constructed_consumer_pairs': 1, 'constructed_families_reused': 1,
    'audit_jobs': 3542, 'audit_dependencies': 74348,
    'historical_warm_rows_live_check': False, 'current_prefix_package_live_check': True,
    'baseline_files': preserved['baseline_files'],
    'unchanged_haskell_files': preserved['unchanged_haskell_files'],
    'actual_lean_lake_jobs': len(unique) - 1, 'capped_command_attempt_receipts': len(unique),
    'receipt_failures_include_one_pre_lean_launch': True,
    'completion_claimed': False}
(HERE / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
