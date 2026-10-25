import hashlib, json, os, shlex, subprocess
from pathlib import Path
area = Path('/tmp/mcfta-main-20261025')
commands = [
 ['nix-shell', '--run', 'export PATH=/usr/bin:$PATH; cabal exec -- ghc-9.14.1 -v0 -threaded -rtsopts -outputdir /tmp/mcfta-main-20261025/public-build -o /tmp/mcfta-main-20261025/public-probe /tmp/mcfta-main-20261025/PublicProbe-v2.hs'],
 [str(area / 'public-probe'), '+RTS', '-N2', '-M1G', '-RTS'],
 ['nix-shell', '--run', 'export PATH=/usr/bin:$PATH; ghc-9.14.1 -v0 -threaded -rtsopts -outputdir /tmp/mcfta-main-20261025/helper-build -o /tmp/mcfta-main-20261025/helper-probe /tmp/mcfta-main-20261025/HelperProbe.hs'],
 [str(area / 'helper-probe'), '+RTS', '-N2', '-M512M', '-RTS']]
for index, command in enumerate(commands, 1):
 result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
 (area / ('probe-v2-' + str(index) + '.log')).write_bytes(result.stdout)
 report = dict(command=command, exit_code=result.returncode, bytes=len(result.stdout), sha256=hashlib.sha256(result.stdout).hexdigest())
 (area / ('probe-v2-' + str(index) + '.json')).write_text(json.dumps(report, indent=2) + '\n')
 print(json.dumps(report), flush=True)
 print(result.stdout.decode(), end='', flush=True)
 if result.returncode:
  raise SystemExit(result.returncode)
