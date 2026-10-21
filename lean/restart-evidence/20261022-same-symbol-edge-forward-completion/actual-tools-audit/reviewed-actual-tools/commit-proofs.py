import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDIT_SHA = '035b57c4aa2f1d23b5e158d06e5672c97673780ee8ba70e65e1809bfe8828a56'
AUDIT_JOBS = int('3625')
AUDIT_DEPENDENCIES = int('75347')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == (HERE / 'starting-head.txt').read_text().strip() == '20f4181948591157e502391e20698138b04b2221'
assert not git('diff', '--cached', '--name-only').strip()
assert git('rev-parse', 'codex/backup-same-symbol-edge-forward-completion-20261022-0026').strip() == (HERE / 'starting-head.txt').read_text().strip()
assert git('rev-parse', 'main').strip() == (HERE / 'starting-local-main.txt').read_text().strip() == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip() == '794903b3fbad3becb8b28736fc33463760731fc7'
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentSameSymbolEdgeForwardCompletion.lean'}
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == next(iter(selected))
assert selected[gate['path']]['sha256'] == gate['sha256'] == hashlib.sha256((HERE / gate['snapshot']).read_bytes()).hexdigest()
assert selected[next(iter(selected))]['strict'] == 'same-symbol-edge-forward-strict-3'
assert selected[next(iter(selected))]['full'] == 'same-symbol-edge-forward-public-1'
assert 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeForwardCompletion.lean' not in json.loads((HERE / 'starting-files.json').read_text())
for name, pin in selected.items():
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256']
    assert data == (HERE / (pin['strict'] + '.source.lean')).read_bytes()
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0
assert json.loads((HERE / 'same-symbol-edge-forward-audit-1.json').read_text())['exit_code'] == 0
audit_raw = (HERE / 'same-symbol-edge-forward-audit-1.log').read_bytes()
assert hashlib.sha256(audit_raw).hexdigest() == AUDIT_SHA
audit = audit_raw.decode()
assert f"Build completed successfully ({AUDIT_JOBS} jobs)." in audit
assert f"{AUDIT_DEPENDENCIES} MicroCFTA theorems" in audit
paths = sorted([*selected, 'lean/MicroCFTA/Audit.lean'])
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original_audit).hexdigest() == '8f02e3994f8b7559692a36eab8e4d1ca0afb31f38485d59d0b5e802f376fa75f'
assert len(original_audit.splitlines()) == 3113
audit_bytes = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
addition = b'import MicroCFTA.SourceCurrentSameSymbolEdgeForwardCompletion\n'
assert audit_bytes.count(addition) == 1 and audit_bytes.replace(addition, b'', 1) == original_audit
assert audit_bytes.index(addition) < audit_bytes.index(b'/-!')
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '-m', 'Prove forward completion of same-symbol edge comparisons'], cwd=ROOT, check=True)
commit = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit.txt').write_text(commit + '\n')
print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'proof_files': paths}))
