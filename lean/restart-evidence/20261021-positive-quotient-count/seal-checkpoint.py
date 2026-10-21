import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
subprocess.run(['/usr/bin/python3', str(HERE / 'verify-checkpoint.py')], check=True)
documents = ['HANDOFF.md', 'NEXT-PROMPT.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md',
             'lean/notes-current-positive-quotient-count.md', 'lean/MicroCFTA/Audit.lean']
documents += list(json.loads((HERE / 'selected-sources.json').read_text()))
entries = []
files = sorted(path for path in HERE.rglob('*') if path.is_file()
               and path.name not in ['scope-manifest.json', 'SHA256SUMS'])
for path in files + [ROOT / name for name in documents]:
    data = path.read_bytes()
    assert len(data) < 90 * 1024 * 1024, path
    entries.append({'path': str(path.relative_to(ROOT)), 'bytes': len(data),
                    'sha256': hashlib.sha256(data).hexdigest()})
(HERE / 'scope-manifest.json').write_text(json.dumps({'files': entries}, indent=2) + '\n')
files.append(HERE / 'scope-manifest.json')
(HERE / 'SHA256SUMS').write_text(''.join(hashlib.sha256(path.read_bytes()).hexdigest()
    + '  ' + str(path.relative_to(HERE)) + '\n' for path in sorted(files)))
print(json.dumps({'status': 'PASS', 'physical_files': len(files), 'scope_entries': len(entries)}))
