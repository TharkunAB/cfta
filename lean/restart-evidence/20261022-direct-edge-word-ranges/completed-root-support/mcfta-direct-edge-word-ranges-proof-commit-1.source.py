import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDIT_SHA = '3fa06af51ce38d71a9b3774fc3c29e0e422ca4a8b27b8de4512de536e2994202'
AUDIT_JOBS = int('3629')
AUDIT_DEPENDENCIES = int('75380')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == (HERE / 'starting-head.txt').read_text().strip() == '108bc09e803b90b5e2e790c796d7ffd3c1d2f39f'
assert not git('diff', '--cached', '--name-only').strip()
assert git('rev-parse', 'codex/backup-direct-edge-word-ranges-20261022-0319').strip() == (HERE / 'starting-head.txt').read_text().strip()
assert git('rev-parse', 'main').strip() == (HERE / 'starting-local-main.txt').read_text().strip() == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip() == '794903b3fbad3becb8b28736fc33463760731fc7'
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentAllocatedDirectEdgeWordRanges.lean'}
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == next(iter(selected))
assert selected[gate['path']]['sha256'] == gate['sha256'] == hashlib.sha256((HERE / gate['snapshot']).read_bytes()).hexdigest()
assert selected[next(iter(selected))]['strict'] == 'direct-edge-word-ranges-strict-1'
assert selected[next(iter(selected))]['full'] == 'direct-edge-word-ranges-public-1'
assert 'lean/MicroCFTA/SourceCurrentAllocatedDirectEdgeWordRanges.lean' not in json.loads((HERE / 'starting-files.json').read_text())
for name, pin in selected.items():
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256']
    assert data == (HERE / (pin['strict'] + '.source.lean')).read_bytes()
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0
assert json.loads((HERE / 'direct-edge-word-ranges-audit-1.json').read_text())['exit_code'] == 0
audit_raw = (HERE / 'direct-edge-word-ranges-audit-1.log').read_bytes()
assert hashlib.sha256(audit_raw).hexdigest() == AUDIT_SHA
audit = audit_raw.decode()
assert f"Build completed successfully ({AUDIT_JOBS} jobs)." in audit
assert f"{AUDIT_DEPENDENCIES} MicroCFTA theorems" in audit
paths = sorted([*selected, 'lean/MicroCFTA/Audit.lean'])
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original_audit).hexdigest() == 'eb67f7c671837d434cc443c9bbe48e2a11bd54c66a3ffbd3bb2506884face11e'
assert len(original_audit.splitlines()) == 3117
audit_bytes = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
addition = b'import MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges\n'
assert audit_bytes.count(addition) == 1 and audit_bytes.replace(addition, b'', 1) == original_audit
assert audit_bytes.index(addition) < audit_bytes.index(b'/-!')
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '-m', 'Bound word ranges for direct edge-body prefixes'], cwd=ROOT, check=True)
commit = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit.txt').write_text(commit + '\n')
print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'proof_files': paths}))
