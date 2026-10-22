import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDIT_SHA = '7e8be4569d2e14ecf95f0ac83511e8ca6e569dde6c70dbb761c51782f386af0b'
AUDIT_JOBS = int('3631')
AUDIT_DEPENDENCIES = int('75384')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == (HERE / 'starting-head.txt').read_text().strip() == '1d5a07b762950272e53c9bd2d5f478d7be39dfad'
assert not git('diff', '--cached', '--name-only').strip()
assert git('rev-parse', 'codex/backup-same-symbol-edge-comparison-20261022-0424').strip() == (HERE / 'starting-head.txt').read_text().strip()
assert git('rev-parse', 'main').strip() == (HERE / 'starting-local-main.txt').read_text().strip() == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip() == '794903b3fbad3becb8b28736fc33463760731fc7'
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparison.lean'}
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == next(iter(selected))
assert selected[gate['path']]['sha256'] == gate['sha256'] == hashlib.sha256((HERE / gate['snapshot']).read_bytes()).hexdigest()
assert selected[next(iter(selected))]['strict'] == 'same-symbol-edge-comparison-strict-1'
assert selected[next(iter(selected))]['full'] == 'same-symbol-edge-comparison-public-1'
assert 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparison.lean' not in json.loads((HERE / 'starting-files.json').read_text())
for name, pin in selected.items():
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256']
    assert data == (HERE / (pin['strict'] + '.source.lean')).read_bytes()
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0
assert json.loads((HERE / 'same-symbol-edge-comparison-audit-1.json').read_text())['exit_code'] == 0
audit_raw = (HERE / 'same-symbol-edge-comparison-audit-1.log').read_bytes()
assert hashlib.sha256(audit_raw).hexdigest() == AUDIT_SHA
audit = audit_raw.decode()
assert f"Build completed successfully ({AUDIT_JOBS} jobs)." in audit
assert f"{AUDIT_DEPENDENCIES} MicroCFTA theorems" in audit
paths = sorted([*selected, 'lean/MicroCFTA/Audit.lean'])
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original_audit).hexdigest() == 'd80480df15a3908dd6c1589b9f6182546d7a4dc09cca9da36098f9289d91c3c6'
assert len(original_audit.splitlines()) == 3119
audit_bytes = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
addition = b'import MicroCFTA.SourceCurrentSameSymbolEdgeComparison\n'
assert audit_bytes.count(addition) == 1 and audit_bytes.replace(addition, b'', 1) == original_audit
assert audit_bytes.index(addition) < audit_bytes.index(b'/-!')
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '-m', 'Complete original-row comparisons across pair-cache branches'], cwd=ROOT, check=True)
commit = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit.txt').write_text(commit + '\n')
print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'proof_files': paths}))
