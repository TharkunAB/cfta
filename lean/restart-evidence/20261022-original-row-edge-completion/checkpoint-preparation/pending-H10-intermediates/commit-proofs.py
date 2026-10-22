import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDIT_SHA = '__H10_AUDIT_SHA__'
AUDIT_JOBS = int('__H10_AUDIT_BUILD_JOBS__')
AUDIT_DEPENDENCIES = int('__H10_AUDIT_DEPENDENCIES__')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == (HERE / 'starting-head.txt').read_text().strip() == 'f985c09f5b18b740082799e15abc4736b3cbf880'
assert not git('diff', '--cached', '--name-only').strip()
assert git('rev-parse', 'codex/backup-same-symbol-edge-ready-20261022-0214').strip() == (HERE / 'starting-head.txt').read_text().strip()
assert git('rev-parse', 'main').strip() == (HERE / 'starting-local-main.txt').read_text().strip() == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip() == '794903b3fbad3becb8b28736fc33463760731fc7'
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentSameSymbolEdgeReady.lean'}
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == next(iter(selected))
assert selected[gate['path']]['sha256'] == gate['sha256'] == hashlib.sha256((HERE / gate['snapshot']).read_bytes()).hexdigest()
assert selected[next(iter(selected))]['strict'] == '__H10_SELECTED_STRICT__'
assert selected[next(iter(selected))]['full'] == '__H10_SELECTED_FULL__'
assert 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeReady.lean' not in json.loads((HERE / 'starting-files.json').read_text())
for name, pin in selected.items():
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256']
    assert data == (HERE / (pin['strict'] + '.source.lean')).read_bytes()
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0
assert json.loads((HERE / '__H10_AUDIT_STEM__.json').read_text())['exit_code'] == 0
audit_raw = (HERE / '__H10_AUDIT_STEM__.log').read_bytes()
assert hashlib.sha256(audit_raw).hexdigest() == AUDIT_SHA
audit = audit_raw.decode()
assert f"Build completed successfully ({AUDIT_JOBS} jobs)." in audit
assert f"{AUDIT_DEPENDENCIES} MicroCFTA theorems" in audit
paths = sorted([*selected, 'lean/MicroCFTA/Audit.lean'])
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original_audit).hexdigest() == 'a36b1f2aefc14b99db041f7b8c40c6c3acc79db4f563b87532fda88b24d392fc'
assert len(original_audit.splitlines()) == 3115
audit_bytes = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
addition = b'import MicroCFTA.SourceCurrentSameSymbolEdgeReady\n'
assert audit_bytes.count(addition) == 1 and audit_bytes.replace(addition, b'', 1) == original_audit
assert audit_bytes.index(addition) < audit_bytes.index(b'/-!')
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '-m', 'Complete ready same-symbol edge comparisons without native execution'], cwd=ROOT, check=True)
commit = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit.txt').write_text(commit + '\n')
print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'proof_files': paths}))
