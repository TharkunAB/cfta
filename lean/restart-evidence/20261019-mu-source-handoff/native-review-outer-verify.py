import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'native-review-outer-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
selection = json.loads((HERE / 'native-review-outer-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'native-review-outer-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in selection['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    checker['check_limits'](stem)
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    if 'source' in meta:
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256'], stem
for path, stem in selection['stricts'].items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert (ROOT / path).read_bytes() == (HERE / meta['source']).read_bytes(), path
    assert (HERE / meta['log']).stat().st_size == 0, stem
meta = json.loads((HERE / 'outer-normal-canonical-2.json').read_text())
log = (HERE / meta['log']).read_text()
warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
assert len(warnings) == 1 and warnings[0].startswith(
    'MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:'), warnings
assert 'Build completed successfully (' in log
assert not re.search(r'error:|sorryAx|failed to pretty print', log)
assert selection['counts'] == manifest['counts']
print(json.dumps({'status': 'PASS', 'files': len(manifest['files']),
    **selection['counts'], 'manifest_sha256': hashlib.sha256(
        (HERE / 'native-review-outer-manifest.json').read_bytes()).hexdigest()}, sort_keys=True))
