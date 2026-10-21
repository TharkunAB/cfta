import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == (HERE / 'starting-head.txt').read_text().strip() == '93f3d0ad7a15196177d4961bcb49092cda94b0e1'
assert not git('diff', '--cached', '--name-only').strip()
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean'}
assert selected[next(iter(selected))]['sha256'] == 'e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
assert selected[next(iter(selected))]['strict'] == 'cold-finite-calls-strict-2'
assert selected[next(iter(selected))]['full'] == 'cold-finite-calls-public-2'
assert 'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean' not in json.loads((HERE / 'starting-files.json').read_text())
for name, pin in selected.items():
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256']
    assert data == (HERE / (pin['strict'] + '.source.lean')).read_bytes()
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0
assert json.loads((HERE / 'audit-1.json').read_text())['exit_code'] == 0
audit_raw = (HERE / 'audit-1.log').read_bytes()
assert hashlib.sha256(audit_raw).hexdigest() == '__H6_AUDIT_SHA__'
audit = audit_raw.decode()
assert f"Build completed successfully ({int('__H6_AUDIT_BUILD_JOBS__')} jobs)." in audit
assert f"{int('__H6_AUDIT_DEPENDENCIES__')} MicroCFTA theorems" in audit
paths = sorted([*selected, 'lean/MicroCFTA/Audit.lean'])
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original_audit).hexdigest() == 'd11e901227fa107e2b36ebd5a76f96f1f89f7f8f697e39be2907011648cf9487'
assert len(original_audit.splitlines()) == 3111
audit_bytes = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
addition = b'import MicroCFTA.SourceCurrentColdFiniteWarmCalls\n'
assert audit_bytes.count(addition) == 1 and audit_bytes.replace(addition, b'', 1) == original_audit
assert audit_bytes.index(addition) < audit_bytes.index(b'/-!')
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '-m', 'Prove finite source-built reduction calls'], cwd=ROOT, check=True)
commit = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit.txt').write_text(commit + '\n')
print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'proof_files': paths}))
