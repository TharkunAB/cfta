import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
output = subprocess.check_output([sys.executable, str(HERE / 'verify-integration.py')],
                                 cwd=ROOT, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
report = json.loads(output)
assert report['status'] == 'PASS'
(HERE / 'integration-verification.json').write_bytes(output)
subprocess.run(['git', 'diff', '--check'], cwd=ROOT, check=True)
documents = [ROOT / name for name in json.loads((HERE / 'current-documents.json').read_text())]
for path in documents:
    assert not any(line != line.rstrip() for line in path.read_text().splitlines()), str(path)
assert not list(HERE.rglob('*.pyc'))
excluded = {'SHA256SUMS', 'root-scope-manifest.json'}
scope = set(documents) | {path for path in HERE.rglob('*') if path.is_file() and path.name not in excluded}
entries = [dict(path=str(path.relative_to(ROOT)), bytes=path.stat().st_size,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest()) for path in sorted(scope)]
(HERE / 'root-scope-manifest.json').write_text(json.dumps({'entries': entries}, indent=2) + '\n')
files = [path for path in sorted(HERE.rglob('*')) if path.is_file() and path.name != 'SHA256SUMS']
(HERE / 'SHA256SUMS').write_text(''.join(hashlib.sha256(path.read_bytes()).hexdigest() + '  '
                                      + str(path.relative_to(ROOT)) + '\n' for path in files))
print(json.dumps({'status': 'PASS', 'scope_pins': len(scope), 'evidence_checksums': len(files),
                  'baseline_files': report['baseline_files'],
                  'all_lean_sources_unchanged': report['all_lean_sources_unchanged'],
                  'typing_outside_haddock_unchanged': report['typing_outside_haddock_unchanged'],
                  'new_lean_jobs': 0}, indent=2))
