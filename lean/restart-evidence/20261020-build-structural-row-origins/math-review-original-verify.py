import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
pins = json.loads((HERE / 'math-review-source-pins.json').read_text())
for entry in pins['files']:
    data = Path(entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
print(json.dumps({'status': 'PASS', 'pins': len(pins['files']),
                  'new_lean_runs': 0, 'owned_pairs': 0,
                  'reused_public_pairs': 2, 'constructed_pairs': 0}))
