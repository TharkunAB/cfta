import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
log = Path('/tmp/mcfta-main-refresh-20261024/typing-probe.log')
commands = [
    'cabal build lib:specftacular lib:specftacular-ghc -j1 --ghc-options=-Werror',
    'cabal exec -- ghc -threaded -rtsopts -Wall -Werror -package specftacular '
    '/tmp/mcfta-main-refresh-20261024-typing-probe.hs -o /tmp/mcfta-main-refresh-20261024-typing-probe',
    '/tmp/mcfta-main-refresh-20261024-typing-probe +RTS -N2 -M512M -RTS'
]
with log.open('xb') as output:
    for command in commands:
        output.write(('COMMAND: ' + command + '\n').encode())
        output.flush()
        result = subprocess.run(['nix-shell', '--run', 'export PATH=/usr/bin:$PATH; ' + command],
                                cwd=root, stdout=output, stderr=subprocess.STDOUT)
        if result.returncode:
            break
print(log.read_text()[-14000:])
raise SystemExit(result.returncode)
