import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'reader-support-manifest.json').read_text())
for item in manifest['entries']:
    path = ROOT / item['path']
    assert path.is_file() and path.stat().st_size == item['bytes'], path
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
selection = json.loads((HERE / 'reader-support-selection.json').read_text())
assert selection['status'] == 'final'
assert selection['counts'] == {'public': 10, 'handwritten': 8, 'constructors': 2,
                              'constructed': 2, 'auxiliary': 0}
spec = importlib.util.spec_from_file_location('checks', HERE / 'reader-support-probe-check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
for group in selection['groups']:
    checks.check_group(group)
selected = [selection['strict'], selection['canonical'], selection['constructed_strict'],
            *[group['name'] for group in selection['groups']]]
attempts = {item['stem']: item['exit_code'] for item in selection['retained_unselected']}
attempts.update({stem: 0 for stem in selected})
assert len(attempts) == 15
for stem, expected in attempts.items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == expected, stem
    checks.check_limits(stem)
    assert meta['wrapper'][1:5] == ['--mem', '4G', '--time', '5m'], stem
    assert meta['command'][0].startswith('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'), stem
    if 'source' in meta:
        assert meta['sha256'] == hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest(), stem
for stem in [selection['strict'], selection['constructed_strict']]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert (HERE / meta['log']).read_bytes() == b'', stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
source = ROOT / selection['production']
assert source.read_bytes() == (HERE / strict['source']).read_bytes()
assert hashlib.sha256(source.read_bytes()).hexdigest() == selection['sha256']
fixture = (HERE / 'reader-support-kernels.lean').read_text()
fixture_strict = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert fixture == (HERE / fixture_strict['source']).read_text()
public_fixture = (HERE / 'reader-support-kernels-public-1.source.lean').read_text().split('#check @')[0]
for option in checks.OPTIONS[1:]:
    public_fixture = public_fixture.replace('set_option ' + option + '\n', '')
assert public_fixture.strip() == fixture.strip()
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (569 jobs).' in log
assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:', log)
assert 'warning:' in (HERE / 'reader-support-direct-3.log').read_text()
assert 'List.Mem 8 [9]' in (HERE / 'reader-support-kernels-6.log').read_text()
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 10,
                  'handwritten_public': 8, 'constructors': 2, 'constructed_pairs': 2,
                  'selected_strict_log_bytes': [0, 0], 'canonical_jobs': 569,
                  'retained_lean_jobs': len(attempts)}))
