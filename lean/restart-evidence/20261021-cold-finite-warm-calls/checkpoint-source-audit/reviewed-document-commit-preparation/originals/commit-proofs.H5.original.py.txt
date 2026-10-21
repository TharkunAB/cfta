import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == (HERE / 'starting-head.txt').read_text().strip() == '8adf2d4aca20ee029de027462bca2878c4c599bf'
assert not git('diff', '--cached', '--name-only').strip()
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentFiniteWarmCalls.lean'}
assert selected[next(iter(selected))]['sha256'] == '984f34529a1050fd015ba0fb742b39cc38e0b518eaae69801cbde1727578a6bd'
assert 'lean/MicroCFTA/SourceCurrentFiniteWarmCalls.lean' not in json.loads((HERE / 'starting-files.json').read_text())
for name, pin in selected.items():
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256']
    assert data == (HERE / (pin['strict'] + '.source.lean')).read_bytes()
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0
assert json.loads((HERE / 'audit-1.json').read_text())['exit_code'] == 0
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3622 jobs).' in audit
assert '75262 MicroCFTA theorems' in audit
paths = sorted([*selected, 'lean/MicroCFTA/Audit.lean'])
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original_audit).hexdigest() == '1013bd1cb1c723049d249b7940b57569cb1c19824b89fae206708db1a4732a11'
audit_bytes = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
addition = b'import MicroCFTA.SourceCurrentFiniteWarmCalls\n'
assert audit_bytes.count(addition) == 1 and audit_bytes.replace(addition, b'', 1) == original_audit
assert audit_bytes.index(addition) < audit_bytes.index(b'/-!')
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '-m', 'Prove finite repeated calls through populated caller state'], cwd=ROOT, check=True)
commit = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit.txt').write_text(commit + '\n')
print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'proof_files': paths}))
