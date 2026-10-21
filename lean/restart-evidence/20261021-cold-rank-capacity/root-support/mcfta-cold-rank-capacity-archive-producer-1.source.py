import subprocess
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261021-cold-rank-capacity')
for source, destination, verifier in [
    ('/tmp/mcfta-cold-rank-capacity-proof', 'cold-capacity', 'cold-rank-capacity-verify.py'),
    ('/tmp/mcfta-cold-rank-capacity-independent-review', 'capacity-independent-review', 'review-verify.py'),
]:
    subprocess.run(['/usr/bin/python3', str(here / 'archive-component.py'),
                    source, destination, verifier], check=True)
