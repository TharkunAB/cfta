import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest_path = HERE / 'mu-observation-manifest.json'
manifest = json.loads(manifest_path.read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.is_file(), item['path']
    assert path.stat().st_size == item['bytes'], item['path']
    assert sha(path) == item['sha256'], item['path']
selection = json.loads((HERE / 'mu-observation-selection.json').read_text())
assert selection['status'] == 'final'
source = HERE / selection['source']
assert sha(source) == selection['source_sha256']
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert strict['exit_code'] == 0
assert (HERE / strict['log']).read_bytes() == b''
assert (HERE / strict['source']).read_bytes() == source.read_bytes()
spec = importlib.util.spec_from_file_location('owned_mu_probe_tools', HERE / 'mu-observation-probe-tools.py')
tools = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tools)
for stem in ['mu-observation-direct-' + str(i) for i in range(1, 10)] + ['mu-observation-public-1']:
    tools.check_limits(stem)
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
    assert meta['command'][1] == '-Dlinter.all=true'
    assert meta['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
    assert sha(HERE / meta['source']) == meta['sha256']
for group in selection['selected_groups']:
    tools.check_group(group)
    meta = json.loads((HERE / (group['name'] + '.json')).read_text())
    assert (HERE / meta['source']).read_bytes().startswith(source.read_bytes())
for stem in selection['reused_canonical']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert not re.search(r'warning|error', (HERE / meta['log']).read_text())
    tools.check_limits(stem)
interface = selection['checked_leaf_interface']
assert sha(HERE / interface['source']) == interface['sha256']
text = source.read_text()
private = re.search(r'private theorem checked_witness(.*?) := by', text, re.S).group(1)
public = re.search(r'theorem native_mu_spine(.*?) := checked_witness formulas solver', text, re.S).group(1)
assert private == public, 'Private and public statements differ'
assert 'SourceCurrentAllocatedGateWorker.primary 8 inputs record.paths (before (bits+2)) = .done true' in public
assert 'SourceCurrentClassObservationSpines.Spine' in public
assert 'SourceEqualityRequiredCache.Keeps finish.checked.native.machine.heap after' in public
assert 'sorry' not in text and not re.search(r'^axiom\b', text, re.M)
assert selection['counts'] == {'owned_production_public': 0, 'constructed': 1, 'auxiliary': 0,
    'selected_full_groups': 1, 'selected_strict_logs': 1, 'owned_lean_jobs': 10}
assert all(item['path'] not in selection['mutable_dependencies_excluded'] for item in manifest['files'])
print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), 'manifest_sha256': sha(manifest_path),
    'source_sha256': sha(source), 'constructed_pairs': 1, 'owned_production_public_pairs': 0,
    'auxiliary_pairs': 0, 'selected_full_groups': 1, 'selected_strict_logs': 1,
    'strict_literal_zero': True, 'private_public_statements_identical': True,
    'primary_true_explicit': True, 'mutable_production_source_excluded': True}, sort_keys=True))
