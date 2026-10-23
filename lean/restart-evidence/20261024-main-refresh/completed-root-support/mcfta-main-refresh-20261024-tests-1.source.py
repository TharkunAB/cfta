import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
log = Path('/tmp/mcfta-main-refresh-20261024/haskell-tests.log')
command = ['nix-shell', '--run',
           'cabal test cfta:unit-tests specftacular:golden -j1 --ghc-options=-Werror '
           '--test-show-details=direct --test-options="+RTS -N1 -RTS"']
with log.open('xb') as output:
    result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
print(log.read_text()[-14000:])
raise SystemExit(result.returncode)
