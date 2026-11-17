from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-third-query-node-seed-check-control-draft'
work = base / '20261117-third-query-node-seed-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller.'
assert Path(__file__).read_bytes() == (control / 'prepare-private-check.py').read_bytes()
selection = json.loads((control / 'SELECTION.json').read_text())
assert selection['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
runtime = base / selection['runtime']
assert not runtime.exists(), 'Preserve earlier attempts and use a fresh runtime.'
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


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
bound.add(control / 'MANIFEST.json')
assert len(selection['components']) == selection['expected_checks'] == 2
assert selection['compile_order'] == [item['module'] for item in selection['components']]
assert selection['expected_axiom_reports'] == 3 and selection['expected_declaration_checks'] == 0
assert not selection['prior_push_required_for_private_check']
assert selection['prior_push_required_before_normal_Source_staging']
prior_work = base / selection['prior_work']
source_path = prior_work / 'SOURCE-COMMIT.json'
publication_path = prior_work / 'PUBLICATION-VERIFIED.json'
source = json.loads(source_path.read_text())
publication = json.loads(publication_path.read_text())
assert source['actual_terminal'] and source['actual_terminal_exit'] == 0
assert source['source_commit'] == selection['source_commit']
assert source['publication_actual_session'] == publication['actual_session'] == 54013
assert publication['actual_terminal'] and publication['actual_terminal_exit'] == 0
assert [item['total_axiom_reports'] for item in publication['checks']] == [702, 4, 297, 702, 702]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] for item in publication['checks'])
assert publication['source_files'] == 6267 and publication['pins_independently_reverified'] == 6872
assert not source['joint_finite_completion_proved'] and not publication['joint_finite_completion_proved']
bound.update([source_path, publication_path])
# Checkpoint/document commits can advance HEAD. Source must stay exactly pinned.
subprocess.run(['git', 'merge-base', '--is-ancestor', source['source_commit'], 'HEAD'], cwd=root, check=True)
subprocess.run(['git', 'diff', '--quiet', source['source_commit'], 'HEAD', '--', 'lean/MicroCFTA'], cwd=root, check=True)
baseline = json.loads((control / selection['source_baseline']).read_text())
assert baseline['source_commit'] == source['source_commit']
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6267 and {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(root / name, record)
seen = set()


def verify_packet(packet, digest):
    manifest_path = packet / 'MANIFEST.json'
    verify(manifest_path, digest)
    if manifest_path in seen:
        return
    seen.add(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    entries = [(item['path'], item) for item in manifest['artifacts']] if 'artifacts' in manifest else records(manifest['files'])
    for name, record in entries:
        verify(packet / name, record)
    pin_path = packet / 'SOURCE-PINS.json'
    if pin_path.exists():
        for name, record in records(json.loads(pin_path.read_text())):
            verify(root / name, record)


normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
candidate_names = set(selection['compile_order'])
raw_sources = {}
normal_imports = set()
for item in selection['components']:
    packet = base / item['packet']
    verify_packet(packet, item['manifest_sha256'])
    raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    if item['kind'] == 'existing_owner_EOF':
        before = verify(root / item['owner_source'], {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
        appended = verify(packet / item['append'], item['append_sha256'])
        assert raw == before + appended
        assert re.findall(rb'^import .*$', raw, re.M) == re.findall(rb'^import .*$', before, re.M)
        declarations = appended
    else:
        assert item['kind'] == 'new_module' and not (root / 'lean/MicroCFTA' / item['source']).exists()
        declarations = raw
        deps = json.loads(verify(packet / item['dependency_file'], item['dependency_sha256']))
        key = selection['components'][0]
        assert deps['freshKeyModule'] == 'MicroCFTA.' + key['module']
        assert deps['freshKeyRaw'] == key['raw_sha256']
        assert (root / deps['freshKeyCandidate']).read_bytes() == (base / key['packet'] / key['source']).read_bytes()
        verify(root / deps['normalOwnerFullAdmission'], deps['normalOwnerFullAdmissionRaw'])
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert not re.search(rb'set_option\s+(maxHeartbeats|maxRecDepth|warningAsError|linter\.)', declarations)
    for header in item['headers']:
        data = verify(packet / header['file'], header['sha256'])
        assert data.rstrip(b'\n') in declarations
    probe = verify(packet / item['probe'], item['probe_sha256'])
    qnames = re.findall(r'^#print axioms (\S+)', probe.decode(), re.M)
    assert qnames == item['public_qnames'] and len(qnames) == item['expected_axiom_reports']
    assert probe.count(b'#check ') == item['expected_declaration_checks'] == 0
    assert len(re.findall(rb'^private theorem ', declarations, re.M)) == item['new_private_theorems']
    assert not re.findall(rb'^(?:private )?def ', declarations, re.M)
    for name in re.findall(rb'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', raw, re.M):
        module = name.decode()
        if module not in candidate_names:
            assert (normal_objects / (module + '.olean')).is_file(), module
            normal_imports.add(module)
    raw_sources[item['module']] = raw + b'\n' + probe
assert sum(item['new_private_theorems'] for item in selection['components']) == selection['new_private_helpers'] == 2
for name in ['check-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((control / name).read_text())

# Root executes this phase only after reviewing the complete preflight.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-third-query-node-seed-check-'))
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
selected['actual_source_commit'] = source['source_commit']
selected['actual_prior_publication'] = publication['actual_session']
selected['prior_checkpoint_push_not_required_for_private_check'] = True
selected['control_manifest_sha256'] = sha((control / 'MANIFEST.json').read_bytes())
(runtime / 'selection.json').write_text(json.dumps(selected, indent=2, sort_keys=True) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({
    str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound)
}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 2,
    'actual_new_public_reports': 3, 'private_helpers_transitive': 2, 'definition_checks': 0,
    'compile_order': selection['compile_order'], 'normal_Source_changed': False,
    'normal_Source_staging_still_requires_prior_checkpoint_push': True}))
