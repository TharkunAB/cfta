import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
entries = json.loads((HERE / 'scope-manifest.json').read_text())['files']
for entry in entries:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
checks = 0
for line in (HERE / 'SHA256SUMS').read_text().splitlines():
    expected, name = line.split('  ', 1)
    assert hashlib.sha256((HERE / name).read_bytes()).hexdigest() == expected, name
    checks += 1
print(json.dumps({'status': 'PASS', 'physical_checksums': checks, 'scope_entries': len(entries)}))
