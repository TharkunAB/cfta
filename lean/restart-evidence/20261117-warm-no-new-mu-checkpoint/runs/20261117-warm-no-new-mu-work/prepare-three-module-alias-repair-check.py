from pathlib import Path
import ast
import hashlib
import json
import re
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-warm-no-new-mu-alias-repair-check-control-draft'
work = base / '20261117-warm-no-new-mu-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller into Work53.'
assert Path(__file__).read_bytes() == (control / 'prepare-three-module-alias-repair-check.py').read_bytes()
selection = json.loads((control / 'SELECTION.json').read_text())
runtime = base / selection['runtime']
assert not runtime.exists(), 'Use a new runtime and preserve earlier attempts.'
sha = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    assert sha(data) == digest, str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


def records(value):
    if isinstance(value, dict):
        return list(value.items())
    return [(item['path'], item) for item in value]


def manifest_records(manifest):
    if 'artifacts' in manifest:
        return [(item['path'], item) for item in manifest['artifacts']]
    return records(manifest['files'])


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
bound.add(control / 'MANIFEST.json')
assert selection['source_commit'] == '3275583d8225d5c6d04fa295c176f9b3bce63996'
assert selection['prior_checkpoint'] == 'a59893a37d6c30b25a92f6ac499e5115057b9383'
assert selection['source_files'] == 6264
assert len(selection['components']) == selection['expected_checks'] == 3
assert selection['compile_order'] == [item['module'] for item in selection['components']]
assert selection['expected_axiom_reports'] == 3 and selection['expected_declaration_checks'] == 0
assert sum(item['private_theorems'] for item in selection['components']) == 46
assert sum(item['private_prop_definitions'] for item in selection['components']) == 4
baseline = json.loads((control / selection['source_baseline']).read_text())
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6264
assert {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain'], **selection['prior_bindings']}.items():
    verify(root / name, record)
for name, record in selection['previous_bindings'].items():
    verify(root / name, record)
failed_runtime = base / selection['previous_failed_run']
assert not (failed_runtime / 'checked.json').exists()
failed = json.loads((failed_runtime / 'results.json').read_text())
rejected = json.loads((root / selection['previous_failure_receipt']).read_text())
assert rejected['actual_session'] == 78575
assert rejected['actual_terminal'] and rejected['actual_terminal_exit'] == 1
assert rejected['run'] == selection['previous_failed_run']
assert rejected['checks'] == failed['checks']
assert [item['exit'] for item in failed['checks']] == [1, 1, 1]
assert [item['diagnostics'] for item in failed['checks']] == [3, 1, 1]
assert failed['checks'][0]['sorryAx'] and 'sorryAx' in failed['checks'][0]['nonstandard_axioms']
assert not failed['proof_credit'] and not rejected['whole_chain_proof_credit']
assert failed['private_helpers_compiled_transitively'] == 0
assert rejected['generated_sorryAx_report_rejected']
assert failed['source_pins_unchanged']
original_selection = json.loads((root / selection['original_selection']).read_text())
assert original_selection['components'][1:] == selection['components'][1:]
original_mu = original_selection['components'][0]
selected_mu = selection['components'][0]
for key, value in original_mu.items():
    if key not in ['packet', 'raw_sha256', 'manifest_sha256']:
        assert selected_mu[key] == value, key
assert selected_mu['packet'] != original_mu['packet']
assert selected_mu['raw_sha256'] != original_mu['raw_sha256']
prior_work = base / selection['prior_work']
source_commit = json.loads((prior_work / 'SOURCE-COMMIT.json').read_text())
assert source_commit['source_commit'] == selection['source_commit']
assert source_commit['actual_terminal'] and source_commit['actual_terminal_exit'] == 0
publication = json.loads((prior_work / 'PUBLICATION-VERIFIED.json').read_text())
assert publication['actual_session'] == 69801 and publication['actual_terminal']
assert publication['actual_terminal_exit'] == 0 and publication['source_files'] == 6264
assert len(publication['checks']) == 5 and all(item['exit'] == 0 for item in publication['checks'])
push = json.loads((prior_work / 'PUSH-VERIFIED.json').read_text())
assert push['source_commit'] == selection['source_commit']
assert push['checkpoint_commit'] == push['remote_commit'] == selection['prior_checkpoint']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0

seen_manifests = set()
checked_pin_manifests = set()


def verify_packet_manifest(path, digest, check_pin_records=False):
    verify(path, digest)
    packet = path.parent
    if path not in seen_manifests:
        seen_manifests.add(path)
        manifest = json.loads(path.read_text())
        for name, record in manifest_records(manifest):
            verify(packet / name, record)
    if not check_pin_records or path in checked_pin_manifests:
        return
    checked_pin_manifests.add(path)
    for pin_file in ['SOURCE-PINS.json', 'ADDITIONAL-SOURCE-PINS.json', 'DEPENDENCY-PINS.json']:
        pin_path = packet / pin_file
        if not pin_path.exists():
            continue
        bound.add(pin_path)
        for name, record in records(json.loads(pin_path.read_text())):
            data_path = root / name
            verify(data_path, record)
            if data_path.name == 'MANIFEST.json':
                pinned_digest = record['sha256'] if isinstance(record, dict) else record
                verify_packet_manifest(data_path, pinned_digest,
                    check_pin_records='independent-review' in data_path.parent.name)
            if isinstance(record, dict) and 'packet_manifest_sha256' in record:
                verify_packet_manifest(data_path.parent / 'MANIFEST.json', record['packet_manifest_sha256'])


raw_sources = {}
normal_imports = set()
candidate_names = set(selection['compile_order'])
normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
for item in selection['components']:
    packet = base / item['packet']
    verify_packet_manifest(packet / 'MANIFEST.json', item['manifest_sha256'], check_pin_records=True)
    raw = verify(packet / item['source'], item['raw_sha256'])
    header = verify(packet / item['header'], item['header_sha256'])
    assert header.rstrip(b'\n') in raw
    probe = verify(packet / item['probe'], item['probe_sha256'])
    assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == [item['public_qname']]
    assert probe.count(b'#print axioms ') == item['expected_axiom_reports'] == 1
    assert probe.count(b'#check ') == item['expected_declaration_checks'] == 0
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert b'set_option maxHeartbeats' not in raw and b'set_option maxRecDepth' not in raw
    assert len(re.findall(r'^private theorem (\w+)', raw.decode(), re.M)) == item['private_theorems']
    assert len(re.findall(r'^private def (\w+)', raw.decode(), re.M)) == item['private_prop_definitions']
    assert not (root / 'lean/MicroCFTA' / (item['module'] + '.lean')).exists()
    for name in re.findall(rb'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', raw, re.M):
        module = name.decode()
        if module not in candidate_names:
            assert (normal_objects / (module + '.olean')).is_file(), module
            normal_imports.add(module)
    raw_sources[item['module']] = raw + b'\n' + probe
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((control / name).read_text())

# Root executes this phase only after the complete preflight succeeds.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-warm-no-new-mu-alias-repair-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for dependency in sorted(normal_objects.glob('*.olean')):
    if dependency.stem not in candidate_names:
        (objects / 'MicroCFTA' / dependency.name).symlink_to(dependency)
        linked.append(dependency.name)
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({
    'normal_objects': str(normal_objects), 'linked_unchanged_modules': linked,
    'excluded_candidate_modules': sorted(candidate_names),
    'verified_direct_normal_imports': sorted(normal_imports),
    'candidate_output_links_created': False, 'cache_data_copied': False,
}, indent=2) + '\n')
source_root = runtime / 'source/MicroCFTA'
source_root.mkdir(parents=True)
for module, raw in raw_sources.items():
    path = source_root / (module + '.lean')
    path.write_bytes(raw)
    bound.add(path)
(runtime / 'shadow-compile.py').write_bytes((control / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((control / 'check-driver.py.txt').read_bytes())
selected = dict(selection)
selected['verified_manifest_paths'] = sorted(str(path.relative_to(root)) for path in seen_manifests)
selected['direct_pin_record_manifests'] = sorted(str(path.relative_to(root)) for path in checked_pin_manifests)
selected['control_manifest_sha256'] = sha((control / 'MANIFEST.json').read_bytes())
(runtime / 'selection.json').write_text(json.dumps(selected, indent=2, sort_keys=True) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({
    str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound)
}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 3,
    'actual_public_reports': 3, 'definition_checks': 0, 'private_explicit_reports': 0,
    'private_helpers_in_selected_sources': 46, 'private_prop_definitions': 4,
    'compile_order': selection['compile_order'], 'normal_source_changed': False}))
