import hashlib,shutil,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta')
H=R/'lean/restart-evidence/20261021-required-shared-target-cap'
source=Path('/tmp/mcfta-required-shared-target-cap-proof/SourceCurrentRequiredSharedTargetCap.lean')
assert hashlib.sha256(source.read_bytes()).hexdigest()=='e6a2c3bb9ce0123877feee3e836770a1ddd24f10a2dd057ef3441feda9bb42cb'
target=R/'lean/MicroCFTA'/source.name
assert not target.exists()
shutil.copyfile(source,target)
for directory,name,verifier in [('/tmp/mcfta-required-shared-target-cap-proof','shared-cap','shared-cap-verify.py'),('/tmp/mcfta-required-shared-target-cap-independent-review','independent-review','verify.py')]:
    subprocess.run(['/usr/bin/python3',str(H/'archive-component.py'),directory,name,verifier],check=True)
