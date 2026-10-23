import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
log = Path('/tmp/mcfta-main-refresh-20261024/type-depth-repro.log')
command = ['nix-shell', '--run', 'export PATH=/usr/bin:$PATH; '
           'cabal exec -- runghc -package=specftacular /tmp/mcfta-main-refresh-20261024-type-depth-repro.hs']
with log.open('xb') as output:
    result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
print(log.read_text())
raise SystemExit(result.returncode)
