from datetime import datetime
from pathlib import Path
import hashlib
import json

base = Path(__file__).resolve().parent
assert not (base / 'pins.json').exists()
assert not (base / 'FROZEN.json').exists()

def identity(path: Path) -> dict:
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

payloads = [
    {'path': str(path.relative_to(base)), **identity(path)}
    for path in sorted(base.rglob('*'))
    if path.is_file() and path.name not in {'pins.json', 'FROZEN.json'}
]
pins = {'schema': 'sha256-payloads-v1', 'root': str(base), 'payloads': payloads}
pins_bytes = (json.dumps(pins, indent=2) + '\n').encode()
(base / 'pins.json').write_bytes(pins_bytes)
seal = {
    'status': 'FROZEN',
    'frozen_at': datetime.now().astimezone().isoformat(),
    'pins': 'pins.json',
    'pins_bytes': len(pins_bytes),
    'pins_sha256': hashlib.sha256(pins_bytes).hexdigest(),
    'payload_count': len(payloads),
    'exact_file_count': len(payloads) + 2,
    'source_records': 77,
    'literal_cuts': 32,
    'document_inverses': 9,
    'report': 'report-final.md',
    'report_sha256': identity(base / 'report-final.md')['sha256'],
    'write_policy': 'WRITE HALT after this seal. No later bundle mutation.',
}
seal_bytes = (json.dumps(seal, indent=2) + '\n').encode()
(base / 'FROZEN.json').write_bytes(seal_bytes)
actual = {str(path.relative_to(base)) for path in base.rglob('*') if path.is_file()}
assert actual == {row['path'] for row in payloads} | {'pins.json', 'FROZEN.json'}
for row in payloads:
    assert identity(base / row['path']) == {key: row[key] for key in ['bytes', 'sha256']}
print(json.dumps({**seal, 'frozen_sha256': hashlib.sha256(seal_bytes).hexdigest()}, indent=2))
