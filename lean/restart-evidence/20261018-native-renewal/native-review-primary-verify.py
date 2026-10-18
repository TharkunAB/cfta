import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'native-review-primary-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], path
    assert sha(path) == entry['sha256'], path
selection = json.loads((HERE / 'native-review-primary-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'native-probe-check.py'))
for group in selection['reused_groups']:
    checker['check_group'](group)
for stem in selection['reused_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ]
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0]
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256']
for path, stem in selection['stricts'].items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert (ROOT / path).read_bytes() == (HERE / meta['source']).read_bytes()
    assert (HERE / meta['log']).stat().st_size == 0
meta = json.loads((HERE / 'selected-primary-canonical-1.json').read_text())
log = (HERE / meta['log']).read_text()
warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
assert len(warnings) == 1
assert warnings[0].startswith('MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:')
assert 'Build completed successfully (1801 jobs).' in log
assert sha(HERE / 'native-review-primary-pins.json') == selection['preserved_production_review_pins']
assert sha(HERE / 'native-manifest.json') == selection['preserved_owned_manifest']
assert selection['counts'] == manifest['counts']
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']), **selection['counts'],
    'strict_log_bytes': 0, 'all_eight_printer_options': True,
    'no_printer_omissions': True, 'standard_axioms_only': True,
    'manifest_sha256': sha(HERE / 'native-review-primary-manifest.json'),
}, sort_keys=True))
