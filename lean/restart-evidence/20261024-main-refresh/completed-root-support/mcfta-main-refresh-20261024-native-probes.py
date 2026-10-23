import shlex
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
folder = Path('/tmp/mcfta-main-refresh-20261024')
probes = [
    (folder / 'CoreIntegrationProbe.hs', 'cfta', folder / 'core-integration-probe', []),
    (Path('/tmp/mcfta-main-refresh-20261024-pruning-inputs/LpoComparatorRegression.hs'),
     'specftacular', folder / 'lpo-comparator-regression', []),
    (Path('/tmp/mcfta-main-refresh-20261024-pruning-inputs/LpoContextRegression.hs'),
     'specftacular', folder / 'lpo-context-regression', []),
    (Path('/tmp/mcfta-main-refresh-20261024-typing-probe.hs'),
     'specftacular', folder / 'typing-probe', ['+RTS', '-N2', '-M512M', '-RTS'])
]
log = folder / 'native-probes.log'
with log.open('xb') as output:
    for source, package, executable, args in probes:
        command = shlex.join(['cabal', 'exec', '--', 'ghc', '-threaded', '-rtsopts',
            '-XOverloadedStrings', '-Wall', '-Werror', '-package', package, str(source), '-o', str(executable)])
        output.write(('COMPILE: ' + command + '\n').encode())
        output.flush()
        result = subprocess.run(['nix-shell', '--run', 'export PATH=/usr/bin:$PATH; ' + command],
                                cwd=root, stdout=output, stderr=subprocess.STDOUT)
        if result.returncode:
            break
        output.write(('RUN: ' + str(executable) + '\n').encode())
        output.flush()
        result = subprocess.run([str(executable), *args], cwd=root, stdout=output, stderr=subprocess.STDOUT)
        if result.returncode:
            break
print(log.read_text()[-16000:])
raise SystemExit(result.returncode)
