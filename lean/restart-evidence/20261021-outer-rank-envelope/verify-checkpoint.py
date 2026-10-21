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
        assert hashlib.sha256((HERE / receipt['source']).read_bytes()).hexdigest() == receipt['sha256']
    if empty:
        assert not (HERE / (stem + '.log')).read_bytes()
    return receipt


audit_source=(ROOT/'lean/MicroCFTA/Audit.lean').read_text()
sources = read('selected-sources.json')
checks = read('selected-checks.json')
for tag, module in [('rank-envelope','SourceCurrentOuterRankEnvelope')]:
    line='import MicroCFTA.'+module+'\n'
    assert audit_source.count(line)==1 and audit_source.index(line)<audit_source.index('run_cmd do')
    name='lean/MicroCFTA/'+module+'.lean'
    digest=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    assert digest==sources[name]['sha256']==checked(checks[tag]['strict'],True)['sha256']
checked('audit-1')
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3616 jobs)' in audit
assert '75112 MicroCFTA theorems' in audit
assert not re.search(r'^error', audit, re.M)
assert all('InternedFreshOrdinaryClosedCompletion.lean' in warning
           for warning in re.findall(r'^warning:.*$', audit, re.M))
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
# A byte-identical receipt from the starting tree records an earlier command.
# Match hashes first, then compare full bytes. Copies do not add jobs.
baseline = read('starting-files.json')
prior_by_sha = {}
for name,pin in baseline.items():
    if name.endswith('.json'):
        prior_by_sha.setdefault(pin['sha256'],[]).append(name)
borrowed = {}
for key in list(unique):
    data=(HERE/unique[key][0]).read_bytes()
    digest=hashlib.sha256(data).hexdigest()
    earlier=prior_by_sha.get(digest,[])
    if not earlier:
        continue
    for name in earlier:
        assert (ROOT/name).read_bytes()==data,name
    for name in unique[key]:
        assert (HERE/name).read_bytes()==data,name
    borrowed[key]={'copies':unique.pop(key),'earlier_receipts':earlier}
write('borrowed-dependency-receipts.json',{'copied_earlier_commands':len(borrowed),'copies_add_jobs':False,'receipts':list(borrowed.values())})
account = {'actual_lean_lake_jobs': len(unique),
    'nonzero_lean_jobs': sum(json.loads(key)['exit_code'] != 0 for key in unique),
    'copies_add_jobs': False, 'copied_earlier_commands':len(borrowed), 'commands': [{'receipts': values, 'exit_code': json.loads(key)['exit_code']}
                                         for key, values in unique.items()]}
assert account['actual_lean_lake_jobs'] == 7 and account['nonzero_lean_jobs'] == 3, account
write('attempt-accounting.json', account)
result = {'status': 'PASS', 'proof': (HERE / 'proof-commit-rank-envelope.txt').read_text().strip(),
    'work_status': 'continuing_at_user_request', 'new_public_theorems': 1, 'new_public_structures': 0, 'new_public_definitions': 1,
    'constructed_consumers': 0, 'audit_jobs': 3616, 'audit_dependencies': 75112,
    'baseline_files': preserved['baseline_files'], 'unchanged_haskell_files': preserved['unchanged_haskell_files'],
    **{key: value for key, value in account.items() if key not in ['commands', 'infrastructure_commands']}, 'completion_claimed': False}
write('verification.json', result)
print(json.dumps(result))
