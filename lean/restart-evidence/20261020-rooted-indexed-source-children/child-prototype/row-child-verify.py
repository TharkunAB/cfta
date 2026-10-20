import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--live-root', type=Path)
args = parser.parse_args()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((HERE / 'row-child-manifest.json').read_text())
for entry in manifest['files']:
    path = HERE / entry['path']
    assert path.is_file(), entry['path']
    assert len(path.read_bytes()) == entry['bytes'], entry['path']
    assert digest(path) == entry['sha256'], entry['path']

selection = json.loads((HERE / 'row-child-selection.json').read_text())
assert selection['finalized']
assert digest(HERE / selection['source']) == selection['sha256']
spec = importlib.util.spec_from_file_location('row_child_probes', HERE / 'row-child-verify-probes.py')
probes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probes)
for group in selection['groups']:
    probes.check_group(group)
for attempt in selection['attempts']:
    stem = attempt['name']
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code'], stem
    assert digest(HERE / meta['source']) == meta['sha256'], stem
    assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean', stem
    assert meta['command'][1] == '-Dlinter.all=true', stem
    assert meta['wrapper'][1:5] == ['--mem', '4G', '--time', '5m'], stem
    probes.check_limits(stem)
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert strict['exit_code'] == 0
assert not (HERE / strict['log']).read_bytes()
assert (HERE / strict['source']).read_bytes() == (HERE / selection['source']).read_bytes()
public = json.loads((HERE / 'row-child-public-1.json').read_text())
assert (HERE / public['source']).read_bytes().startswith((HERE / selection['source']).read_bytes())
pins = json.loads((HERE / 'row-child-source-pins.json').read_text())
for entry in pins['files']:
    copy = HERE / entry['copy']
    assert len(copy.read_bytes()) == entry['bytes'], entry['copy']
    assert digest(copy) == entry['sha256'], entry['copy']
    if args.live_root:
        live = args.live_root / entry['path']
        assert live.read_bytes() == copy.read_bytes(), entry['path']
assert not list(HERE.glob('**/__pycache__'))
print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), **selection['counts'],
                  'live_inputs': bool(args.live_root)}))
