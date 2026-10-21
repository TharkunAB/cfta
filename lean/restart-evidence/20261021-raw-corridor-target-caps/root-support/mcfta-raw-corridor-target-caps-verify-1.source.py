import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


def checked(stem, empty=False):
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0, stem
    assert read(stem + '.limits.json') == {'memory.max': '4294967296',
        'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = read(stem + '.usage.json')
    assert usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
    wrapper = receipt['wrapper']
    assert wrapper[wrapper.index('--mem') + 1] == '4G'
    assert wrapper[wrapper.index('--time') + 1] == '5m'
    if 'source' in receipt:
        assert hashlib.sha256(((HERE / stem).parent / receipt['source']).read_bytes()).hexdigest() == receipt['sha256']
    if empty:
        assert not (HERE / (stem + '.log')).read_bytes()
    return receipt


audit_source=(ROOT/'lean/MicroCFTA/Audit.lean').read_text()
sources = read('selected-sources.json')
checks = read('selected-checks.json')['strict']
for name, entry in sources.items():
    line='import MicroCFTA.'+Path(name).stem+'\n'
    assert audit_source.count(line)==1 and audit_source.index(line)<audit_source.index('run_cmd do')
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==entry['sha256']
    assert checked(checks[name],True)['sha256']==entry['sha256']
checked('audit-1')
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3573 jobs)' in audit
assert '74785 MicroCFTA theorems' in audit
assert not re.search(r'^error', audit, re.M)
assert all('InternedFreshOrdinaryClosedCompletion.lean' in warning
           for warning in re.findall(r'^warning:.*$', audit, re.M))
assert {item['path'] for item in read('components.json')} == {'raw-corridor','projection-cap','target-cap','independent-review','class-plan'}
for item in read('components.json'):
    for mode in [[], ['--live']]:
        subprocess.run(['/usr/bin/python3', str(HERE / item['path'] / item['verifier']),
                        *item['extra'], *mode], cwd='/', check=True, stdout=subprocess.DEVNULL)
preserved = json.loads(subprocess.check_output(['/usr/bin/python3', str(HERE / 'verify-preservation.py')], text=True))
write('preservation-final.json', preserved)
unique = {}
for path in HERE.rglob('*.json'):
    if 'previous-publication-support' in path.parts:
        continue
    try:
        receipt = json.loads(path.read_text())
    except ValueError:
        continue
    if (isinstance(receipt, dict) and isinstance(receipt.get('command'), list)
            and receipt['command'] and Path(receipt['command'][0]).name in ['lean', 'lake']
            and 'wrapper' in receipt and isinstance(receipt.get('exit_code'), int)):
        unique.setdefault(json.dumps(receipt, sort_keys=True), []).append(str(path.relative_to(HERE)))
account = {'actual_lean_lake_jobs': len(unique),
    'nonzero_lean_jobs': sum(json.loads(key)['exit_code'] != 0 for key in unique),
    'copies_add_jobs': False, 'commands': [{'receipts': values, 'exit_code': json.loads(key)['exit_code']}
                                         for key, values in unique.items()]}
assert account['actual_lean_lake_jobs'] == 14 and account['nonzero_lean_jobs'] == 1, account
write('attempt-accounting.json', account)
result = {'status': 'PASS', 'proof': (HERE / 'proof-commit-corridor-cap.txt').read_text().strip(),
    'goal_status': 'active', 'new_public_theorems': 6, 'new_public_inductives': 1, 'new_public_definitions': 0,
    'constructed_consumers': 0, 'canonical_jobs': 3, 'prelaunch_tool_timeouts': 1, 'audit_jobs': 3573, 'audit_dependencies': 74785,
    'baseline_files': preserved['baseline_files'], 'unchanged_haskell_files': preserved['unchanged_haskell_files'],
    **{key: value for key, value in account.items() if key not in ['commands', 'infrastructure_commands']}, 'completion_claimed': False}
write('verification.json', result)
print(json.dumps(result))
