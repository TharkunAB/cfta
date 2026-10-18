import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'used-mu-review-manifest.json').read_text())
for item in manifest['entries']:
    path = ROOT / item['path']
    assert path.is_file() and path.stat().st_size == item['bytes'], path
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
selection = json.loads((HERE / 'used-mu-review-selection.json').read_text())
assert selection['status'] == 'final'
assert selection['counts'] == {
    'new_public_pairs': 0, 'new_constructed_pairs': 1, 'new_auxiliary_pairs': 0,
    'reused_public_pairs': 9, 'reused_constructed_pairs': 2,
}
spec = importlib.util.spec_from_file_location('checks', HERE / 'used-mu-review-probe-check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
for group in selection['selected_groups'] + selection['reused_groups']:
    checks.check_group(group)

def execution(stem):
    meta = json.loads((HERE / (stem + '.json')).read_text())
    checks.check_limits(stem)
    if 'source' in meta:
        assert meta['sha256'] == hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest(), stem
    return meta, (HERE / meta['log']).read_bytes()

for stem in [selection['strict'], *selection['reused_strict'].values(), *selection['reused_constructed_strict']]:
    meta, log = execution(stem)
    assert meta['exit_code'] == 0 and log == b'', stem
for module, stem in selection['reused_strict'].items():
    meta, _ = execution(stem)
    assert (ROOT / 'lean/MicroCFTA' / (module + '.lean')).read_bytes() == (HERE / meta['source']).read_bytes()
for stem in selection['reused_canonical']:
    meta, log = execution(stem)
    assert meta['exit_code'] == 0 and b'Build completed successfully' in log, stem
for stem in selection['failures']:
    meta, log = execution(stem)
    assert meta['exit_code'] == 1 and b'error' in log, stem
for stem in selection['unselected_success']:
    meta, log = execution(stem)
    assert meta['exit_code'] == 0 and log == b'', stem
for stem in selection['unselected_printer_failure']:
    meta, log = execution(stem)
    assert meta['exit_code'] == 0 and b'failed to pretty print' in log, stem

old = (HERE / 'used-mu-review-counterexample-4.source.lean').read_text()
new = (HERE / 'used-mu-review-counterexample-5.source.lean').read_text()
def statement(source, name):
    start = source.index('theorem ' + name + ' :') + len('theorem ' + name + ' :')
    return source[start:source.index(' :=', start)]
def proof(source, name, end):
    start = source.index('theorem ' + name + ' :')
    start = source.index(' := by', start) + len(' := by')
    return source[start:source.index(end, start)].strip()
assert statement(old, 'nested_binder_boundary') == statement(new, 'nested_binder_boundary') == statement(new, 'checked')
assert proof(old, 'nested_binder_boundary', 'end MicroCFTA.UsedMuRootEraseBoundary') == proof(new, 'checked', '/-- A nested unused binder exposes an outer bare name')
assert (HERE / 'used-mu-review-counterexample.lean').read_bytes() == (HERE / 'used-mu-review-counterexample-5.source.lean').read_bytes()
assert (HERE / 'used-mu-review-counterexample-public.lean').read_bytes() == (HERE / 'used-mu-review-counterexample-public-2.source.lean').read_bytes()
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), **selection['counts'], 'selected_groups': 1, 'reused_groups': 4, 'strict_log_bytes': 0}))
