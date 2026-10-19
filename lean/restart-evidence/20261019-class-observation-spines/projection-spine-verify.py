import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


checks = runpy.run_path(str(HERE / 'verify-probes.py'))
selection = json.loads((HERE / 'projection-spine-selection.json').read_text())
manifest = json.loads((HERE / 'projection-spine-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert sha(path) == entry['sha256'] and path.stat().st_size == entry['bytes'], entry['path']
for stem in manifest['attempts']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    checks['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert strict['exit_code'] == 0 and not (HERE / strict['log']).read_bytes()
assert sha(HERE / strict['source']) == sha(ROOT / selection['production']) == selection['sha256']
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert canonical['exit_code'] == 0 and 'Build completed successfully' in log
assert len(re.findall(r'^warning:', log, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in log
assert not re.search(r'\berror:', log)
checks['check_group'](selection['group'])
print(json.dumps({'status': 'PASS', 'public_pairs': 2, 'constructed_pairs': 0,
                  'strict_empty_logs': 1, 'owned_runs': len(manifest['attempts']),
                  'pins': len(manifest['files'])}))
