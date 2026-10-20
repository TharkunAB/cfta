import hashlib
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
source = Path('/tmp/mcfta-native-generated-row-capture-backedge-fixture')
manifest = source / 'backedge-kernels-manifest.json'
assert hashlib.sha256(manifest.read_bytes()).hexdigest() == sys.argv[1]
selection = json.loads((source / 'backedge-kernels-selection.json').read_text())
assert selection['finalized']
destination = HERE / 'capture-fixture'
assert not destination.exists()
shutil.copytree(source, destination)
assert hashlib.sha256((destination / manifest.name).read_bytes()).hexdigest() == sys.argv[1]
items = json.loads((HERE / 'archived-components.json').read_text())
items.append({'path': 'capture-fixture', 'manifest': manifest.name,
              'manifest_sha256': sys.argv[1]})
(HERE / 'archived-components.json').write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'manifest_sha256': sys.argv[1],
                  'source': selection['source']}))
