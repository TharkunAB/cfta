import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'class-rows-independent-review-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
source = ROOT / 'lean/MicroCFTA/SourceCurrentClassFoldRowOrigins.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == 'd57ecf4371ed53c17ca0f64feb30994764612cac51483eb36a207a0f5fa4faab'
assert source.read_bytes() == (HERE / 'class-rows-direct-10.source.lean').read_bytes()
assert (HERE / 'class-rows-direct-10.log').read_bytes() == b''
for stem in ['class-rows-direct-10', 'class-rows-canonical-2']:
    receipt = json.loads((HERE / (stem + '.json')).read_text())
    assert receipt['exit_code'] == 0, stem
    assert json.loads((HERE / receipt['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
log = (HERE / 'class-rows-canonical-2.log').read_text()
assert 'Build completed successfully (1434 jobs).' in log
assert len(re.findall(r'^warning:', log, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in log
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'read_only_review': True, 'independent_builds': 0}))
