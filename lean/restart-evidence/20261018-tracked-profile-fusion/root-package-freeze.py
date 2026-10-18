import hashlib
import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261018-tracked-profile-fusion'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


components = [name.removesuffix('-manifest.json') for name in json.loads((HERE/'component-manifests.json').read_text())]
reports = []
for prefix in components:
    reports.append((prefix + '-verify.py', 'root-component-' + prefix + '-verification.json'))
reports += [('verify-checkpoint.py', 'checkpoint-validation.json'),
            ('verify-preservation.py', 'preservation-final.json')]
for script, report in reports:
    result = json.loads(subprocess.check_output(
        ['python3', str(HERE / script)], cwd=ROOT,
        env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}))
    assert result['status'] == 'PASS', (script, result)
    (HERE / report).write_text(json.dumps(result, indent=2) + '\n')
    print(report, 'PASS')

names = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
         'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
         'lean/notes-proof-status-20261017.md', 'lean/MicroCFTA/Audit.lean',
         'lean/notes-current-tracked-profile-fusion.md']
evidence = ['CONTINUE-initial.md', 'ROOT-SCOPE.md', 'NEXT.md', 'root-reviewed-components.md', 'checkpoint-validation.json',
            'preservation-final.json', 'selected-strict.json', 'selected-canonical.json',
            'selected-groups.json', 'selected-constructed-strict.json',
            'selection-status.json', 'selected-audit.json', 'component-manifests.json',
            'expected-counts.json', 'proof-commit.txt', 'new-modules.json', 'frozen-modules.json', 'root-package-select.py', 'root-package-docs.py', 'root-package-freeze.py', 'root-freeze-components.py',
            'starting-head.txt', 'starting-tree.txt', 'starting-sha256.json',
            'starting-stashes.txt', 'starting-worktrees.txt', 'verify-checkpoint.py',
            'verify-preservation.py', 'verify-closure.py']
evidence += [report for _, report in reports]
paths = [ROOT / name for name in names] + [HERE / name for name in evidence]
(HERE / 'root-scope-manifest.json').write_text(json.dumps({
    'entries': [{'path': str(path.relative_to(ROOT)), 'sha256': sha(path)}
                for path in sorted(set(paths))],
}, indent=2) + '\n')
files = sorted(path for path in HERE.rglob('*') if path.is_file() and path.name != 'SHA256SUMS')
(HERE / 'SHA256SUMS').write_text(''.join(
    sha(path) + '  ' + str(path.relative_to(ROOT)) + '\n' for path in files))
stage = [ROOT / name for name in names] + sorted(path for path in HERE.rglob('*') if path.is_file())
Path('/tmp/mcfta-tracked-profile-fusion-stage.nul').write_bytes(b''.join(
    str(path.relative_to(ROOT)).encode() + b'\0' for path in stage))
print('Frozen checksums:', len(files))
print('Stage files:', len(stage))
