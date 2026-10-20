import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'kernels-manifest.json').read_text())
for entry in manifest['files']:
    path = HERE / entry['path']
    data = path.read_bytes()
    assert len(data) == entry['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], str(path)
spec = importlib.util.spec_from_file_location('kernel_probes', HERE / 'verify-probes.py')
probes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probes)
selection = json.loads((HERE / 'kernels-selection.json').read_text())
for group in selection['groups']:
    probes.check_group(group)
strict = selection['strict']
meta = json.loads((HERE / (strict + '.json')).read_text())
assert meta['exit_code'] == 0
assert not (HERE / meta['log']).read_bytes()
assert (HERE / meta['source']).read_bytes() == (HERE / selection['source']).read_bytes()
probes.check_limits(strict)
assert hashlib.sha256((HERE / selection['production_dependency']).read_bytes()).hexdigest() == selection['production_sha256']
assert not list(HERE.glob('**/__pycache__'))
print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']),
                  'owned_public_pairs': 0, 'constructed_pairs': 1,
                  'lean_runs': 2, 'canonical_runs': 0}))
