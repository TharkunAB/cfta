import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
environment = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}


def read(name):
    return json.loads((HERE / name).read_text())


def entry(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(ROOT)), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


for script, target in [('verify-checkpoint.py', 'checkpoint-validation.json'),
                       ('verify-preservation.py', 'preservation-final.json')]:
    output = subprocess.check_output([sys.executable, str(HERE / script)], cwd=ROOT, env=environment)
    report = json.loads(output)
    assert report['status'] == 'PASS', script
    (HERE / target).write_bytes(output)
assert not list(HERE.rglob('*.pyc'))
subprocess.run(['git', 'diff', '--check'], cwd=ROOT, check=True)
docs = [ROOT / name for name in read('current-documents.json')]
modules = [ROOT / 'lean/MicroCFTA' / (name + '.lean') for name in read('new-modules.json')]
for path in docs + modules:
    assert not any(line != line.rstrip() for line in path.read_text().splitlines()), str(path)
(HERE / 'whitespace-policy.json').write_text(json.dumps({
    'current_sources_and_documents': 'git diff --check and direct trailing-space checks pass',
    'immutable_evidence': 'Keep raw attempt, printer, log and copied status bytes unchanged.'}, indent=2) + '\n')
excluded = {'SHA256SUMS', 'root-scope-manifest.json'}
restored = {ROOT / item['original'] for item in read('compressed-evidence.json')}
paths = set(docs + modules)
paths.update(path for path in HERE.rglob('*')
             if path.is_file() and path.name not in excluded and path not in restored)
(HERE / 'root-scope-manifest.json').write_text(json.dumps({'entries': [entry(p) for p in sorted(paths)]}, indent=2) + '\n')
files = [path for path in sorted(HERE.rglob('*'))
         if path.is_file() and path.name != 'SHA256SUMS' and path not in restored]
assert all(path.stat().st_size < 90 * 1024 * 1024 for path in files)
(HERE / 'SHA256SUMS').write_text(''.join(hashlib.sha256(path.read_bytes()).hexdigest() + '  '
                                      + str(path.relative_to(ROOT)) + '\n' for path in files))
print(json.dumps({'status': 'PASS', 'scope_pins': len(paths), 'evidence_checksums': len(files),
                  **read('checkpoint-validation.json')}, indent=2))
