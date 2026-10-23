import hashlib
import shlex
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
folder = Path('/tmp/mcfta-main-refresh-20261024')
originals = Path('/tmp/mcfta-main-refresh-20261024-pruning-inputs')
comparator = (originals / 'LpoComparatorRegression.hs').read_text()
assert comparator.count('tail xs') == 1
comparator = comparator.replace('tail xs', 'drop 1 xs')
for label, value in [('s/t, t/u, u/s', 'raw'), ('after canonicalTypes', 'canonical')]:
    before = 'print ("' + label + '", ' + value + ')'
    assert comparator.count(before) == 1
    comparator = comparator.replace(before, 'putStrLn ("' + label + ': " ++ show ' + value + ')')
context = (originals / 'LpoContextRegression.hs').read_text()
for label, value in [('compare (f a) a', 'before'), ('compare ((f a) x) (a x)', 'inside')]:
    before = 'print ("' + label + '", ' + value + ')'
    assert context.count(before) == 1
    context = context.replace(before, 'putStrLn ("' + label + ': " ++ show ' + value + ')')
for name, source in [('RootLpoComparatorRegression.hs', comparator), ('RootLpoContextRegression.hs', context)]:
    target = folder / name
    assert not target.exists()
    target.write_text(source)
probes = [(folder / 'RootLpoComparatorRegression.hs', 'lpo-comparator-regression', []),
          (folder / 'RootLpoContextRegression.hs', 'lpo-context-regression', []),
          (Path('/tmp/mcfta-main-refresh-20261024-typing-probe.hs'), 'typing-probe',
           ['+RTS', '-N2', '-M512M', '-RTS'])]
log = folder / 'pending-probes-v2.log'
with log.open('xb') as output:
    for source, name, args in probes:
        executable = folder / name
        command = shlex.join(['cabal', 'exec', '--', 'ghc', '-threaded', '-rtsopts',
            '-XOverloadedStrings', '-Wall', '-Werror', '-package', 'specftacular', '-package', 'cfta',
            str(source), '-o', str(executable)])
        output.write(('SOURCE SHA256: ' + hashlib.sha256(source.read_bytes()).hexdigest() + '\nCOMPILE: ' + command + '\n').encode())
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
print(log.read_text()[-14000:])
raise SystemExit(result.returncode)
