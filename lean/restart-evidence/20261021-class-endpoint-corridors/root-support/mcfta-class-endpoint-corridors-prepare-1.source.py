import subprocess
from pathlib import Path
H=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261021-class-endpoint-corridors')
for command in [
    ['archive-component.py','/tmp/mcfta-class-endpoint-corridor-independent-review','independent-review','verify.py'],
    ['prepare-checkpoint.py'],
    ['update-documents.py']]:
    subprocess.run(['/usr/bin/python3',str(H/command[0]),*command[1:]],check=True)
