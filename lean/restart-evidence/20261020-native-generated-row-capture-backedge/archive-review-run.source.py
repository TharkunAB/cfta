import hashlib
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
source = Path('/tmp/mcfta-native-generated-row-capture-backedge-fixture-review')
manifest = source / 'fixture-review-manifest.json'
assert hashlib.sha256(manifest.read_bytes()).hexdigest() == sys.argv[1]
destination = HERE / 'fixture-review'
assert not destination.exists()
shutil.copytree(source, destination)
assert hashlib.sha256((destination / manifest.name).read_bytes()).hexdigest() == sys.argv[1]
items = json.loads((HERE / 'archived-components.json').read_text())
items.append({'path': 'fixture-review', 'manifest': manifest.name,
              'manifest_sha256': sys.argv[1]})
(HERE / 'archived-components.json').write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'manifest_sha256': sys.argv[1]}))
