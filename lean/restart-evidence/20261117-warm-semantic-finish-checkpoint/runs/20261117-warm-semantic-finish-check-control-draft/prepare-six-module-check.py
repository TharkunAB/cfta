from pathlib import Path
import ast
import hashlib
import json
import re
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-warm-semantic-finish-check-control-draft'
work = base / '20261117-warm-semantic-finish-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller to Work52.'
sha = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((control / 'SELECTION.json').read_text())
runtime = base / selection['runtime']
assert not runtime.exists(), 'Use a new runtime; preserve previous results.'
assert Path(__file__).read_bytes() == (control / 'prepare-six-module-check.py').read_bytes()


def verify_record(path, record):
    data = path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    assert sha(data) == digest, str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    return data


def manifest_items(manifest):
    if 'artifacts' in manifest:
        return [(item['path'], item) for item in manifest['artifacts']]
    files = manifest['files']
    if isinstance(files, dict):
        return list(files.items())
    assert isinstance(files, list)
    return [(item.get('path', item.get('file')), item) for item in files]


def pin_items(pins):
    if isinstance(pins, dict):
        return list(pins.items())
    assert isinstance(pins, list)
    return [(item['path'], item) for item in pins]


bound_files = set()
control_manifest = json.loads((control / 'MANIFEST.json').read_text())
for name, record in control_manifest['files'].items():
    verify_record(control / name, record)
    bound_files.add(control / name)
bound_files.add(control / 'MANIFEST.json')
assert selection['source_commit'] == '4f765463a45a0962aeb6411548b987a8aa0274e1'
assert selection['source_files'] == 6258
assert len(selection['components']) == selection['expected_checks'] == 6
assert selection['compile_order'] == [item['module'] for item in selection['components']]
assert sum(item['expected_axiom_reports'] for item in selection['components']) == 5
assert sum(item['expected_declaration_checks'] for item in selection['components']) == 3
baseline = json.loads((control / selection['source_baseline']).read_text())
current_sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(current_sources) == 6258
assert {str(path.relative_to(root)) for path in current_sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify_record(root / name, record)
    bound_files.add(root / name)
for name, record in selection['prior_bindings'].items():
    verify_record(root / name, record)
    bound_files.add(root / name)
prior_work = base / selection['prior_work']
stage = json.loads((prior_work / 'SOURCES-NORMAL-STAGING.json').read_text())
source_commit = json.loads((prior_work / 'SOURCE-COMMIT.json').read_text())
publication = json.loads((prior_work / 'PUBLICATION-VERIFIED.json').read_text())
assert source_commit['source_commit'] == selection['source_commit']
assert source_commit['actual_terminal'] and source_commit['actual_terminal_exit'] == 0
assert publication['actual_session'] == 82650
assert publication['actual_terminal'] and publication['actual_terminal_exit'] == 0
assert len(publication['checks']) == 5 and all(item['exit'] == 0 for item in publication['checks'])
assert publication['source_files'] == stage['source_files'] == 6258
current_components = {item['source_path']: item for item in stage['components']}
overrides = stage['baseline_overrides']
historical_resolutions = []


def verify_historical_pin(name, record):
    path = root / name
    digest = record['sha256'] if isinstance(record, dict) else record
    current = path.read_bytes()
    if sha(current) == digest:
        verify_record(path, record)
        bound_files.add(path)
        return
    assert name in overrides, name
    old_path = root / overrides[name]
    old = verify_record(old_path, record)
    assert name in baseline['sources']
    verify_record(path, baseline['sources'][name])
    if name in current_components:
        component = current_components[name]
        assert current.startswith(old) and sha(current) == component['raw_sha256'], name
    else:
        assert name == 'lean/MicroCFTA/Audit.lean', name
        offset = stage['old_audit_exact_offset']
        assert current[offset:offset + len(old)] == old
    bound_files.update([path, old_path])
    historical_resolutions.append({'path': name, 'historical_sha256': digest,
                                   'baseline_snapshot': overrides[name],
                                   'current_sha256': sha(current)})


raw_sources = {}
seen_packets = set()
for component in selection['components']:
    packet = base / component['packet']
    manifest_path = packet / 'MANIFEST.json'
    assert sha(manifest_path.read_bytes()) == component['manifest_sha256']
    if packet not in seen_packets:
        seen_packets.add(packet)
        manifest = json.loads(manifest_path.read_text())
        bound_files.add(manifest_path)
        for name, record in manifest_items(manifest):
            verify_record(packet / name, record)
            bound_files.add(packet / name)
        source_pins = packet / 'SOURCE-PINS.json'
        if source_pins.exists():
            for name, record in pin_items(json.loads(source_pins.read_text())):
                verify_historical_pin(name, record)
        dependency_pins = packet / 'DEPENDENCY-PINS.json'
        if dependency_pins.exists():
            for name, record in pin_items(json.loads(dependency_pins.read_text())):
                verify_record(root / name, record)
                bound_files.add(root / name)
                if isinstance(record, dict) and 'packet_manifest_sha256' in record:
                    related_manifest = (root / name).parent / 'MANIFEST.json'
                    assert sha(related_manifest.read_bytes()) == record['packet_manifest_sha256']
                    bound_files.add(related_manifest)
    raw = verify_record(packet / component['source'], component['raw_sha256'])
    header = verify_record(packet / component['header'], component['header_sha256'])
    assert header.rstrip(b'\n') in raw, component['module']
    assert b'set_option maxHeartbeats' not in raw and b'set_option maxRecDepth' not in raw
    assert b'#print axioms ' not in raw, 'Count only the selected appended reports.'
    probes = verify_record(packet / component['probe'], component['probe_sha256'])
    assert probes.count(b'#print axioms ') == component['expected_axiom_reports']
    assert probes.count(b'#check ') == component['expected_declaration_checks']
    for name in component['declaration_names']:
        assert ('#check ' + name + '\n').encode() in probes
    assert not (root / 'lean/MicroCFTA' / (component['module'] + '.lean')).exists()
    raw_sources[component['module']] = raw + b'\n' + probes
original = selection['original_af8_header']
old_header = verify_record(root / original['path'], original['sha256'])
assert old_header == (base / selection['components'][-1]['packet'] / selection['components'][-1]['header']).read_bytes()
bound_files.add(root / original['path'])
for template in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((control / template).read_text())
candidate_names = set(selection['compile_order'])
normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
normal_imports = set()
for raw in raw_sources.values():
    for name in re.findall(rb'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', raw, re.M):
        module = name.decode()
        if module not in candidate_names:
            assert (normal_objects / (module + '.olean')).is_file(), module
            normal_imports.add(module)

# All input checks precede runtime and object allocation.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-warm-semantic-finish-check-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for dependency in sorted(normal_objects.glob('*.olean')):
    if dependency.stem in candidate_names:
        continue
    (objects / 'MicroCFTA' / dependency.name).symlink_to(dependency)
    linked.append(dependency.name)
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({
    'normal_objects': str(normal_objects), 'linked_unchanged_modules': linked,
    'verified_direct_normal_imports': sorted(normal_imports),
    'excluded_candidate_modules': sorted(candidate_names),
    'candidate_output_links_created': False, 'cache_data_copied': False,
}, indent=2) + '\n')
source_root = runtime / 'source/MicroCFTA'
source_root.mkdir(parents=True)
for module, raw in raw_sources.items():
    source = source_root / (module + '.lean')
    source.write_bytes(raw)
    bound_files.add(source)
(runtime / 'shadow-compile.py').write_bytes((control / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((control / 'check-driver.py.txt').read_bytes())
selected = dict(selection)
selected['historical_pin_resolutions'] = historical_resolutions
selected['control_manifest_sha256'] = sha((control / 'MANIFEST.json').read_bytes())
(runtime / 'selection.json').write_text(json.dumps(selected, indent=2, sort_keys=True) + '\n')
bound_files.add(Path(__file__))
bound_files.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({
    str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound_files)
}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects),
                  'checks': 6, 'actual_public_reports': 5, 'definition_checks': 3,
                  'compile_order': selection['compile_order'], 'normal_source_changed': False}))
