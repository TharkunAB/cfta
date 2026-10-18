import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'class-rows-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
checks = runpy.run_path(str(HERE / 'verify-probes.py'))
groups = [('class-rows-public-1', 27),
          ('class-rows-fold-kernels-public-1', 2),
          ('class-rows-rebuild-kernels-public-1', 1)]
for stem, count in groups:
    checks['check_group']({'name': stem, 'pairs': count, 'full_proof': True})
for path in HERE.glob('class-rows-*.json'):
    receipt = json.loads(path.read_text())
    if 'exit_code' not in receipt:
        continue
    stem = path.stem
    checks['check_limits'](stem)
    if 'source' in receipt:
        source = HERE / receipt['source']
        assert source.is_absolute()
        assert checks['sha'](source) == receipt['sha256'], stem
        assert receipt['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(source)], stem
for stem in ['class-rows-direct-10', 'class-rows-fold-kernels-1',
             'class-rows-rebuild-kernels-1']:
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == 0
    assert not (HERE / receipt['log']).read_bytes(), stem
production = ROOT / 'lean/MicroCFTA/SourceCurrentClassFoldRowOrigins.lean'
assert production.read_bytes() == (HERE / 'class-rows-direct-10.source.lean').read_bytes()
canonical = json.loads((HERE / 'class-rows-canonical-2.json').read_text())
assert canonical['exit_code'] == 0
assert 'Build completed successfully (1434 jobs).' in (HERE / canonical['log']).read_text()
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
                  'public_pairs': 27, 'constructed_pairs': 3,
                  'strict_empty': True, 'canonical_jobs': 1434}))
