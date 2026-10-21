import hashlib
import json
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
source, name = Path(sys.argv[1]), sys.argv[2]
assert source.is_dir() and '/' not in name
target = HERE / name
assert not target.exists()
shutil.copytree(source, target)
files = {}
for path in sorted(target.rglob('*')):
    if path.is_file():
        relative = path.relative_to(target)
        assert path.read_bytes() == (source / relative).read_bytes()
        files[str(relative)] = hashlib.sha256(path.read_bytes()).hexdigest()
registry = HERE / 'archived-components.json'
items = json.loads(registry.read_text())
assert name not in items
items[name] = files
registry.write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'component': name, 'archived_files': len(files)}))
