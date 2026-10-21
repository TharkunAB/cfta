import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
stems = []
for receipt in Path('/tmp').glob('mcfta-class-positive-chronology-*.json'):
    value = json.loads(receipt.read_text())
    if isinstance(value, dict) and 'wrapper' in value and 'exit_code' in value:
        stems.append(receipt.name.removesuffix('.json'))
for stem in sorted(stems):
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.is_file(), source
        target = HERE / 'root-support' / source.name
        if target.exists():
            assert target.read_bytes() == source.read_bytes(), source
        else:
            shutil.copyfile(source, target)
print(json.dumps({'status': 'PASS'}))
