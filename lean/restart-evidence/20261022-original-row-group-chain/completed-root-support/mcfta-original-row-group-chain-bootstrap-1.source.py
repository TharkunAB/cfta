import ast
import difflib
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
old = root / 'lean/restart-evidence/20261022-prepend-grouping'
here = root / 'lean/restart-evidence/20261022-original-row-group-chain'
assert not here.exists()
assert json.loads(Path('/tmp/mcfta-original-row-group-chain-initial-pull-1.json').read_text())['exit_code'] == 0
here.mkdir()
pins = {}
for name in ['root-driver.py','root-capped-worker.py','root-run-check.py','archive-extra.py','archive-packages.py','start.py']:
    before = (old / name).read_text()
    after = before
    if name == 'root-driver.py':
        after = after.replace('20261022-prepend-grouping','20261022-original-row-group-chain')
    if name == 'start.py':
        after = after.replace('d0cf685f461430a7c608ceb3b76da0fe568e4d84','70787b95484cb69897bc4075858e07c7f9c22433')
        after = after.replace('backup-prepend-grouping-20261022-2245','backup-original-row-group-chain-20261022-2345')
        after = after.replace('/tmp/mcfta-original-row-cluster-language-local-publication.json','/tmp/mcfta-prepend-grouping-local-publication.json')
        begin = after.index('env = dict(os.environ,')
        end = after.index("assert git('rev-parse', 'HEAD').decode().strip() == START",begin)
        replacement = "pull = Path('/tmp/mcfta-original-row-group-chain-initial-pull-1.json')\nassert json.loads(pull.read_text())['exit_code'] == 0\n(HERE / 'initial-pull-receipt.json').write_bytes(pull.read_bytes())\n(HERE / 'pull.log').write_bytes(Path('/tmp/mcfta-original-row-group-chain-initial-pull.log').read_bytes())\n"
        after = after[:begin] + replacement + after[end:]
        after = after.replace('import os\n','')
    ast.parse(after)
    (here / name).write_text(after)
    if before != after:
        (here / (name + '.H21-original.txt')).write_text(before)
        (here / (name + '.patch')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='H21/' + name,tofile='H22/' + name)))
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
driver = Path('/tmp/mcfta-original-row-group-chain-driver.py')
assert not driver.exists()
driver.write_bytes((here / 'root-driver.py').read_bytes())
(here / 'bootstrap-pins.json').write_text(json.dumps(pins,indent=2) + '\n')
print(json.dumps(dict(status='PREPARED',helpers=6,proof_jobs=0,pull_reused_without_repeat=True)))
