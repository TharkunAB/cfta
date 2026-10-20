import hashlib
import json
from pathlib import Path
import shutil

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261020-native-generated-row-capture-backedge')
source = Path('/tmp/mcfta-backedge-normalized-prefix-helper')
digest = '3f25dad8ac9cd3db349f9cff8076a045c19bfe89c88263dfbf10684c98ec8e17'
assert hashlib.sha256((source / 'helper-manifest.json').read_bytes()).hexdigest() == digest
destination = here / 'prefix-helper'
assert not destination.exists()
shutil.copytree(source, destination)
assert hashlib.sha256((destination / 'helper-manifest.json').read_bytes()).hexdigest() == digest
print(json.dumps({'status': 'PASS', 'manifest_sha256': digest, 'pins': 57,
                  'actual_jobs': 8, 'failed_jobs': 6, 'native_checkpoint_validated': False}))
