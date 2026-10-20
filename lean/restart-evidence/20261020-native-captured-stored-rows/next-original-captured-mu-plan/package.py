import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def pin(path):
    data = (HERE / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


files = ['plan.md', 'historical-v1-plan.md', 'historical-v1.json', 'source-pins.json',
         'selection.json', 'verify.py', 'package.py']
sources = json.loads((HERE / 'source-pins.json').read_text())['files']
(HERE / 'manifest.json').write_text(json.dumps({
    'schema': 1, 'files': [pin(path) for path in files], 'sources': sources}, indent=2) + '\n')
