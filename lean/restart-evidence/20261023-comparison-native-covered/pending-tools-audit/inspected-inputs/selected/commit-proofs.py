import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDIT_SHA = '__H28_AUDIT_SHA__'
AUDIT_JOBS = int('__H28_AUDIT_BUILD_JOBS__')
AUDIT_DEPENDENCIES = int('__H28_AUDIT_DEPENDENCIES__')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == (HERE / 'starting-head.txt').read_text().strip() == 'b796e8e660a73ac328d41cad53c61099ba79d93f'
assert not git('diff', '--cached', '--name-only').strip()
assert git('rev-parse', 'codex/backup-comparison-native-covered-20261023-0601').strip() == (HERE / 'starting-head.txt').read_text().strip()
assert git('rev-parse', 'main').strip() == (HERE / 'starting-local-main.txt').read_text().strip() == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip() == '794903b3fbad3becb8b28736fc33463760731fc7'
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparisonCovered.lean'}
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == next(iter(selected))
assert selected[gate['path']]['sha256'] == gate['sha256'] == hashlib.sha256((HERE / gate['snapshot']).read_bytes()).hexdigest()
assert selected[next(iter(selected))]['strict'] == '__H28_SELECTED_STRICT_STEM__'
assert selected[next(iter(selected))]['full'] == '__H28_SELECTED_FULL_STEM__'
assert 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparisonCovered.lean' not in json.loads((HERE / 'starting-files.json').read_text())
for name, pin in selected.items():
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256']
    assert data == (HERE / (pin['strict'] + '.source.lean')).read_bytes()
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0
assert json.loads((HERE / '__H28_AUDIT_STEM__.json').read_text())['exit_code'] == 0
audit_raw = (HERE / '__H28_AUDIT_STEM__.log').read_bytes()
assert hashlib.sha256(audit_raw).hexdigest() == AUDIT_SHA
audit = audit_raw.decode()
assert f"Build completed successfully ({AUDIT_JOBS} jobs)." in audit
assert f"{AUDIT_DEPENDENCIES} MicroCFTA theorems" in audit
paths = sorted([*selected, 'lean/MicroCFTA/Audit.lean'])
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original_audit).hexdigest() == '393f9390294b78b458a9d8529a1bf405836bbba6af1f0cec4b6f310a27feca8d'
assert len(original_audit.splitlines()) == 3133
audit_bytes = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
addition = b'import MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered\n'
assert audit_bytes.count(addition) == 1 and audit_bytes.replace(addition, b'', 1) == original_audit
assert audit_bytes.index(addition) < audit_bytes.index(b'/-!')
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '-m', json.loads('__H28_PROOF_COMMIT_MESSAGE_JSON__')], cwd=ROOT, check=True)
commit = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit.txt').write_text(commit + '\n')
print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'proof_files': paths}))
