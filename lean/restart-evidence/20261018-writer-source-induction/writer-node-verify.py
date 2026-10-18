import ast
import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


checks = runpy.run_path(str(HERE / 'verify-probes.py'))
for entry in read('writer-node-manifest.json')['entries']:
    path = ROOT / entry['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256'], entry['path']
    assert path.stat().st_size == entry['bytes'], entry['path']
selection = read('writer-node-selection.json')
checks['check_group'](selection['groups'][0])
assert selection['groups'][0] == {
    'name': 'writer-node-public-1', 'pairs': 5, 'kind': 'new-public', 'full_proof': True}
strict = selection['strict']
receipt = read(strict + '.json')
assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
assert checks['sha'](HERE / receipt['source']) == checks['sha'](
    ROOT / 'lean/MicroCFTA/SourceCurrentWriterFiniteNodeAlignment.lean')
checks['check_limits'](strict)
canonical = selection['canonical']
receipt = read(canonical + '.json')
log = (HERE / receipt['log']).read_text()
assert receipt['exit_code'] == 0 and 'Build completed successfully (635 jobs).' in log
assert not re.search(r'^warning:', log, re.M)
checks['check_limits'](canonical)
for name in ['writer-node-verify.py', 'root-run-check.py', 'root-capped-worker.py', 'verify-probes.py']:
    ast.parse((HERE / name).read_text(), filename=name)
print(json.dumps({'status': 'PASS', 'public_pairs': 5, 'constructed_pairs': 0,
                  'entries': len(read('writer-node-manifest.json')['entries']), 'strict_modules': 1}))
