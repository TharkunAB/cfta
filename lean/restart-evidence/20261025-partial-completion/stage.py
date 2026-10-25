import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
relative = Path('lean/restart-evidence/20261025-partial-completion')
evidence = root / relative
manifest = json.loads((evidence / 'manifest.json').read_text())
for name, expected in manifest.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    data = (evidence / name).read_bytes()
    assert len(data) == expected['bytes'] and hashlib.sha256(data).hexdigest() == expected['sha256']
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md',
             'lean/notes-current-pruning-enumeration-callback-completion.md']
subprocess.run(['git', 'add', '-f', '--', *documents], cwd=root, check=True)
payloads = [str(relative / name) for name in manifest] + [str(relative / 'manifest.json')]
subprocess.run(['git', 'add', '-f', '--', *payloads], cwd=root, check=True)
for name in payloads + documents:
    staged = subprocess.check_output(['git', 'show', ':' + name], cwd=root)
    assert staged == (root / name).read_bytes(), name
subprocess.run(['git', 'diff', '--cached', '--check', '--', *documents], cwd=root, check=True)
print(json.dumps(dict(verified_indexed_payloads=len(payloads), verified_documents=len(documents))))
