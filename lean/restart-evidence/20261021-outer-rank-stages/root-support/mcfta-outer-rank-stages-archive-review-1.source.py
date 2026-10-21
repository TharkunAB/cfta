import json
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
source, destination, verifier, *extra = sys.argv[1:]
target = HERE / destination
assert not target.exists()
shutil.copytree(source, target)
for mode in [[], ['--live']]:
    subprocess.run(['/usr/bin/python3', str(target / verifier), '--root', str(ROOT), *extra, *mode],
                   cwd='/', check=True, stdout=subprocess.DEVNULL)
registry = HERE / 'components.json'
items = json.loads(registry.read_text()) if registry.exists() else []
items.append({'path': destination, 'verifier': verifier, 'extra': ['--root', str(ROOT), *extra], 'live': True})
registry.write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'component': destination}))
