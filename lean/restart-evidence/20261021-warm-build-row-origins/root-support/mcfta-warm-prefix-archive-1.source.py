import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
source, name, manifest, verifier = sys.argv[1:]
source = Path(source)
target = HERE / name
assert not target.exists()
subprocess.run(['/usr/bin/python3', str(source / verifier), '--live'], check=True)
shutil.copytree(source, target)
subprocess.run(['/usr/bin/python3', str(target / verifier)], check=True, cwd='/')
subprocess.run(['/usr/bin/python3', str(target / verifier), '--live'], check=True, cwd='/')
digest = hashlib.sha256((target / manifest).read_bytes()).hexdigest()
report = {'path': name, 'manifest': manifest, 'manifest_sha256': digest,
          'verifier': verifier, 'portable_verified': True, 'live_verified': True}
(HERE / (name + '-archive.json')).write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
