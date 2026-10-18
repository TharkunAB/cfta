import hashlib
import json
import runpy
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'outer-row-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
checks = runpy.run_path(str(HERE / 'verify-probes.py'))
for stem, count in [('outer-row-public-1', 11), ('outer-row-kernels-public-1', 1)]:
    checks['check_group']({'name': stem, 'pairs': count, 'full_proof': True})
for path in HERE.glob('outer-row-*.json'):
    receipt = json.loads(path.read_text())
    if not isinstance(receipt, dict) or 'exit_code' not in receipt:
        continue
    checks['check_limits'](path.stem)
    if 'source' in receipt:
        source = HERE / receipt['source']
        assert source.is_absolute()
        assert checks['sha'](source) == receipt['sha256'], path.name
        assert receipt['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(source)], path.name
for stem in ['outer-row-direct-9', 'outer-row-kernels-2']:
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == 0
    assert not (HERE / receipt['log']).read_bytes()
source = ROOT / 'lean/MicroCFTA/SourceCurrentOuterRowFieldOrigins.lean'
assert source.read_bytes() == (HERE / 'outer-row-direct-9.source.lean').read_bytes()
canonical = json.loads((HERE / 'outer-row-canonical-1.json').read_text())
assert canonical['exit_code'] == 0
assert 'Build completed successfully (1830 jobs).' in (HERE / canonical['log']).read_text()
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
                  'public_pairs': 11, 'constructed_pairs': 1,
                  'strict_empty': True, 'canonical_jobs': 1830}))
