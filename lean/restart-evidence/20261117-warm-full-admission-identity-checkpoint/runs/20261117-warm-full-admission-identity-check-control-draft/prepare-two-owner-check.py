from pathlib import Path
import ast
import hashlib
import json
import re
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-warm-full-admission-identity-check-control-draft'
work = base / '20261117-warm-full-admission-identity-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller into Work54.'
assert Path(__file__).read_bytes() == (control / 'prepare-two-owner-check.py').read_bytes()
selection = json.loads((control / 'SELECTION.json').read_text())
runtime = base / selection['runtime']
assert not runtime.exists(), 'Use a fresh runtime and preserve earlier attempts.'
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
    return list(value.items()) if isinstance(value, dict) else [(item['path'], item) for item in value]


def artifact_records(manifest):
    if 'artifacts' in manifest:
        return [(item['path'], item) for item in manifest['artifacts']]
    return records(manifest['files'])


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
bound.add(control / 'MANIFEST.json')
assert selection['source_commit'] == 'ebce743f365aad5e98c31a5e4eb6415fbd50c958'
assert selection['source_files'] == 6267
assert len(selection['components']) == selection['expected_checks'] == 2
assert selection['compile_order'] == [item['module'] for item in selection['components']]
assert selection['expected_axiom_reports'] == 4 and selection['expected_declaration_checks'] == 0
baseline = json.loads((control / selection['source_baseline']).read_text())
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6267
assert {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain'], **selection['prior_bindings']}.items():
    verify(root / name, record)
prior_work = base / selection['prior_work']
source_commit = json.loads((prior_work / 'SOURCE-COMMIT.json').read_text())
assert source_commit['source_commit'] == selection['source_commit']
assert source_commit['actual_terminal'] and source_commit['actual_terminal_exit'] == 0
publication = json.loads((prior_work / 'PUBLICATION-VERIFIED.json').read_text())
assert publication['actual_session'] == 29997 and publication['actual_terminal']
assert publication['actual_terminal_exit'] == 0 and publication['source_files'] == 6267
assert len(publication['checks']) == 5 and all(item['exit'] == 0 for item in publication['checks'])

# Root runs this controller only after the preceding checkpoint push is verified.
push_path = root / selection['prior_push_verified_receipt']
push = json.loads(push_path.read_text())
assert push['source_commit'] == selection['source_commit']
assert push['checkpoint_commit'] == push['remote_commit']
assert re.fullmatch(r'[0-9a-f]{40}', push['checkpoint_commit'])
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
bound.add(push_path)
seen_manifests = set()
checked_pin_manifests = set()


def verify_packet(path, digest, check_pins=False):
    verify(path, digest)
    packet = path.parent
    if path not in seen_manifests:
        seen_manifests.add(path)
        for name, record in artifact_records(json.loads(path.read_text())):
            verify(packet / name, record)
    if not check_pins or path in checked_pin_manifests:
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
                digest = record['sha256'] if isinstance(record, dict) else record
                verify_packet(data_path, digest, check_pins='independent-review' in data_path.parent.name)
            if isinstance(record, dict) and 'packet_manifest_sha256' in record:
                verify_packet(data_path.parent / 'MANIFEST.json', record['packet_manifest_sha256'])


normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
candidate_names = set(selection['compile_order'])
normal_imports = set()
raw_sources = {}
for item in selection['components']:
    packet = base / item['packet']
    verify_packet(packet / 'MANIFEST.json', item['manifest_sha256'], check_pins=True)
    assembly_data = verify(packet / item['assembly'], item['assembly_sha256'])
    assembly = json.loads(assembly_data)
    assert assembly['baseOwner'] == item['owner_source']
    assert assembly['baseBytes'] == item['owner_bytes'] and assembly['baseSha256'] == item['owner_sha256']
    assert assembly['append'] == item['append'] and assembly['appendSha256'] == item['append_sha256']
    assert assembly['candidate'] == item['source'] and assembly['candidateSha256'] == item['raw_sha256']
    if 'byteExactPrefix' in assembly:
        assert assembly['byteExactPrefix'] and assembly['importsAdded'] == []
        assert assembly['publicProbeCount'] == 2 and assembly['privateProbeCount'] == 1
    else:
        assert assembly['byteExactBasePrefix'] and assembly['newImports'] == []
        assert assembly['expectedNewPublicReports'] == 2
    before = verify(root / item['owner_source'], {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
    snapshot = verify(control / item['owner_snapshot'], {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
    assert before == snapshot
    appended = verify(packet / item['append'], item['append_sha256'])
    raw = verify(packet / item['source'], item['raw_sha256'])
    assert raw == before + appended
    assert re.findall(rb'^import .*$', raw, re.M) == re.findall(rb'^import .*$', before, re.M)
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert b'set_option maxHeartbeats' not in appended and b'set_option maxRecDepth' not in appended
    for header in item['headers']:
        data = verify(packet / header['file'], header['sha256'])
        assert data.rstrip(b'\n') in appended
    probe = verify(packet / item['probe'], item['probe_sha256'])
    qnames = re.findall(r'^#print axioms (\S+)', probe.decode(), re.M)
    assert qnames == item['public_qnames'] and len(qnames) == item['expected_axiom_reports'] == 2
    assert probe.count(b'#check ') == item['expected_declaration_checks'] == 0
    public_names = re.findall(r'^theorem (\w+)', appended.decode(), re.M)
    assert [name.rsplit('.', 1)[1] for name in qnames] == public_names
    assert len(re.findall(r'^private theorem (\w+)', appended.decode(), re.M)) == item['new_private_theorems']
    assert not re.findall(r'^(?:private )?def ', appended.decode(), re.M)
    for name in re.findall(rb'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', raw, re.M):
        module = name.decode()
        if module not in candidate_names:
            assert (normal_objects / (module + '.olean')).is_file(), module
            normal_imports.add(module)
    raw_sources[item['module']] = raw + b'\n' + probe
assert sum(item['new_private_theorems'] for item in selection['components']) == 1
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((control / name).read_text())

# Root executes this phase only after the complete preflight succeeds.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-warm-full-admission-identity-check-'))
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
selected['actual_prior_checkpoint'] = push['checkpoint_commit']
selected['control_manifest_sha256'] = sha((control / 'MANIFEST.json').read_bytes())
(runtime / 'selection.json').write_text(json.dumps(selected, indent=2, sort_keys=True) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({
    str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound)
}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 2,
    'actual_new_public_reports': 4, 'definition_checks': 0, 'new_private_explicit_reports': 0,
    'new_private_helpers_selected_for_transitive_check': 1, 'new_prop_definitions': 0,
    'old_owner_prefixes_byte_exact': True, 'fresh_credit_for_old_owner_theorems': 0,
    'compile_order': selection['compile_order'], 'normal_source_changed': False}))
