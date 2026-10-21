import subprocess
from pathlib import Path
H=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261021-raw-corridor-target-caps')
for source,target,verifier in [
    ('/tmp/mcfta-required-raw-corridor-proof','raw-corridor','raw-corridor-verify.py'),
    ('/tmp/mcfta-required-raw-corridor-projection-proof','projection-cap','raw-projection-verify.py'),
    ('/tmp/mcfta-raw-corridor-shared-target-cap-proof','target-cap','target-verify.py'),
    ('/tmp/mcfta-class-endpoint-corridor-plan','class-plan','plan-verify.py')]:
    subprocess.run(['/usr/bin/python3',str(H/'archive-component.py'),source,target,verifier],check=True)
