import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


checks = runpy.run_path(str(HERE / 'verify-probes.py'))
manifest = read('root-plain-manifest.json')
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], item['path']
for stem in manifest['attempts']:
    meta = read(stem + '.json')
    checks['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
old = (ROOT / 'lean/restart-evidence/20261019-recursive-value-ancestry/full-audit-1.log').read_text()
warnings = re.findall(r'^warning:.*$', old, re.M)
assert len(warnings) == 1
for module, selected in read('root-plain-selection.json')['modules'].items():
    production = ROOT / 'lean/MicroCFTA' / (module + '.lean')
    strict = read(selected['strict'] + '.json')
    assert strict['exit_code'] == 0 and not (HERE / strict['log']).read_bytes()
    assert sha(production) == sha(HERE / strict['source']) == selected['sha256']
    canonical = read(selected['canonical'] + '.json')
    log = (HERE / canonical['log']).read_text()
    assert canonical['exit_code'] == 0 and 'Build completed successfully' in log
    assert re.findall(r'^warning:.*$', log, re.M) == warnings
    checks['check_group'](selected['group'])
print(json.dumps({'status': 'PASS', 'production_modules': 2, 'public_pairs': 5,
                  'constructed_pairs': 0, 'strict_empty_logs': 2,
                  'owned_runs': len(manifest['attempts']), 'pins': len(manifest['files'])}))
