import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
source, expected = sys.argv[1:]
source = Path(source)
target = ROOT / 'lean/MicroCFTA' / source.name
assert not target.exists()
data = source.read_bytes()
assert hashlib.sha256(data).hexdigest() == expected
target.write_bytes(data)
print(json.dumps({'status': 'PASS', 'source': str(target.relative_to(ROOT)), 'sha256': expected}))
