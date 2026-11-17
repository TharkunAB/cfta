from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-numerical-source-callbacks-repair-check-control-draft'
work = base / '20261117-numerical-source-callbacks-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller.'
assert Path(__file__).read_bytes() == (control / 'prepare-repair-check.py').read_bytes()
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
assert selection['expected_checks'] == len(selection['components']) == 3
component_by_module = {item['module']: item for item in selection['components']}
assert len(component_by_module) == 3 and set(selection['compile_order']) == set(component_by_module)
assert selection['expected_axiom_reports'] == 3 and selection['expected_declaration_checks'] == 1
assert selection['new_private_helpers'] == selection['new_prop_definitions'] == 1
assert not selection['prior_checkpoint_push_required_for_private_check']
assert selection['prior_checkpoint_push_required_before_normal_Source_staging']
prior_work = base / selection['prior_work']
source_path = prior_work / 'SOURCE-COMMIT.json'
publication_path = prior_work / 'PUBLICATION-VERIFIED.json'
stage_path = prior_work / 'SOURCES-NORMAL-STAGING.json'
source = json.loads(source_path.read_text())
publication = json.loads(publication_path.read_text())
stage = json.loads(stage_path.read_text())
assert source['actual_terminal'] and source['actual_terminal_exit'] == 0
assert source['source_commit'] == selection['source_commit']
assert source['publication_actual_session'] == publication['actual_session'] == selection['prior_publication_actual_session'] == 60614
assert publication['actual_terminal'] and publication['actual_terminal_exit'] == 0
assert [item['total_axiom_reports'] for item in publication['checks']] == [709, 7, 304, 709, 709]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] for item in publication['checks'])
assert publication['source_files'] == 6270 and publication['pins_independently_reverified'] == 7160
assert publication['audited_theorems'] == 100129
assert not publication['joint_finite_completion_proved']
assert stage['baseline_overrides'] == selection['historical_overrides']
bound.update([source_path, publication_path, stage_path])
# Documentation commits may advance HEAD. All compiler inputs stay identical.
subprocess.run(['git', 'merge-base', '--is-ancestor', source['source_commit'], 'HEAD'], cwd=root, check=True)
subprocess.run(['git', 'diff', '--quiet', source['source_commit'], 'HEAD', '--', 'lean/MicroCFTA'], cwd=root, check=True)
baseline = json.loads(verify(root / selection['source_baseline_path'], selection['source_baseline_sha256']))
assert baseline['source_commit'] == source['source_commit']
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6270 and {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(root / name, record)
staged_owner_by_path = {item['source_path']: item for item in stage['components']
    if item['kind'] == 'existing_owner_EOF'}
historical_substitutions = []


def verify_candidate_pin(name, record):
    current_path = root / name
    current = current_path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    if sha(current) == digest:
        verify(current_path, record)
        return
    assert name in selection['historical_overrides'] and name in staged_owner_by_path, name
    owner = staged_owner_by_path[name]
    old_path = root / selection['historical_overrides'][name]
    old = verify(old_path, record)
    assert current == verify(current_path, owner['raw_sha256'])
    assert len(old) == owner['old_bytes'] and sha(old) == owner['old_sha256']
    assert current.startswith(old) and owner['append_offset'] == len(old)
    historical_substitutions.append({'source': name, 'historical_snapshot': str(old_path.relative_to(root)),
        'old_sha256': digest, 'new_sha256': sha(current), 'old_bytes': len(old),
        'entire_old_prefix_preserved': True, 'raw_equality_claimed': False})


# Preserve actual95793 and the original source/header artifacts.
failed_runtime = base / selection['first_failed_runtime']
rejected_path = root / selection['first_failure_receipt']
rejected = json.loads(rejected_path.read_text())
failed_result_path = failed_runtime / 'results.json'
failed_result = json.loads(failed_result_path.read_text())
assert rejected['actual_session'] == selection['first_failed_session'] == 95793
assert rejected['actual_terminal'] and rejected['actual_exit'] == 1
assert rejected['checks'] == failed_result['checks'] and not rejected['proof_credit']
assert rejected['generated_sorryAx_reports_rejected']
assert [item['diagnostics'] for item in rejected['checks']] == [1, 6]
assert not (failed_runtime / 'checked.json').exists()
bound.update([rejected_path, failed_result_path])
for record in json.loads((control / 'FAILURE-PINS.json').read_text())['artifacts']:
    verify(root / record['path'], record)
comparison = json.loads((control / 'FIRST-COMPARISON.json').read_text())
for entry in comparison['components']:
    original = verify(root / entry['original'], entry['original_sha256'])
    repaired = verify(root / entry['repaired'], entry['repaired_sha256'])
    if entry['kind'] == 'semicolon_only':
        assert original != repaired
        assert original.replace(b'(let binder := pair entry.identity entry.identity\n',
            b'(let binder := pair entry.identity entry.identity;\n', 1) == repaired
    else:
        assert entry['kind'] == 'byte_exact' and original == repaired
# Push is now verified. Keep it bound for later normal staging; private input
# validity still comes from the source commit, publication and exact baseline.
push_path = root / selection['source55_push_receipt']
push = json.loads(push_path.read_text())
assert push['source_commit'] == selection['source_commit']
assert push['checkpoint_commit'] == push['remote_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
bound.add(push_path)

normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
candidate_names = set(component_by_module)
raw_sources = {}
normal_imports = set()
for item in selection['components']:
    packet = base / item['packet']
    manifest_path = packet / 'MANIFEST.json'
    manifest = json.loads(verify(manifest_path, item['manifest_sha256']))
    for name, record in records(manifest['files']):
        verify(packet / name, record)
    for name, record in records(json.loads((packet / 'SOURCE-PINS.json').read_text())):
        verify_candidate_pin(name, record)
    raw = verify(packet / item['source'], {'bytes': item['raw_bytes'], 'sha256': item['raw_sha256']})
    assert not (root / 'lean/MicroCFTA' / item['source']).exists()
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert not re.search(rb'set_option\s+(maxHeartbeats|maxRecDepth|warningAsError|linter\.)', raw)
    assert len(re.findall(rb'^private theorem ', raw, re.M)) == item['new_private_theorems']
    assert len(re.findall(rb'^(?:private )?def ', raw, re.M)) == item['new_prop_definitions']
    if item['new_prop_definitions']:
        definition = verify(packet / item['definition_file'], item['definition_sha256'])
        assert definition.rstrip(b'\n') in raw and b': Prop :=' in definition
        assert re.findall(rb'^(?:private )?def (\w+)', raw, re.M) == [b'Seeds']
    for header in item['headers']:
        data = verify(packet / header['file'], header['sha256'])
        assert data.rstrip(b'\n') in raw
    probe = verify(packet / item['probe'], item['probe_sha256'])
    assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['public_qnames']
    assert probe.count(b'#print axioms ') == item['expected_axiom_reports'] == 1
    assert probe.count(b'#check ') == 0
    if item.get('declaration_probe'):
        declaration_probe = verify(packet / item['declaration_probe'], item['declaration_probe_sha256'])
        assert re.findall(r'^#check (\S+)', declaration_probe.decode(), re.M) == item['declaration_names']
        assert declaration_probe.count(b'#check ') == item['expected_declaration_checks'] == 1
        probe += b'\n' + declaration_probe
    else:
        assert item['expected_declaration_checks'] == 0
    raw_sources[item['module']] = raw + b'\n' + probe
    for name in re.findall(rb'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', raw, re.M):
        module = name.decode()
        if module not in candidate_names:
            assert (normal_objects / (module + '.olean')).is_file(), module
            normal_imports.add(module)
# Check transitive normal imports as well as the candidate's direct imports.
get_imports = lambda data: [name.decode() for name in re.findall(rb'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', data, re.M)]
import_graph = {path.stem: get_imports(path.read_bytes()) for path in sources}
import_graph.update({module: get_imports(raw) for module, raw in raw_sources.items()})
position = {module: index for index, module in enumerate(selection['compile_order'])}
for module in component_by_module:
    pending = list(import_graph[module])
    seen = set()
    while pending:
        imported = pending.pop()
        if imported in seen:
            continue
        seen.add(imported)
        if imported in component_by_module:
            assert position[imported] < position[module], (module, imported)
        else:
            pending.extend(import_graph.get(imported, []))
for name in ['check-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((control / name).read_text())

# Root executes this phase only after reviewing every preflight check.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-numerical-source-callbacks-repair-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for dependency in sorted(normal_objects.glob('*.olean')):
    if dependency.stem not in candidate_names:
        (objects / 'MicroCFTA' / dependency.name).symlink_to(dependency)
        linked.append(dependency.name)
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'normal_objects': str(normal_objects),
    'linked_unchanged_modules': linked, 'excluded_candidate_modules': sorted(candidate_names),
    'verified_direct_normal_imports': sorted(normal_imports), 'candidate_output_links_created': False,
    'cache_data_copied': False}, indent=2) + '\n')
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
selected['historical_substitutions_used'] = historical_substitutions
selected['control_manifest_sha256'] = sha((control / 'MANIFEST.json').read_bytes())
(runtime / 'selection.json').write_text(json.dumps(selected, indent=2, sort_keys=True) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): sha(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 3,
    'public_reports': 3, 'private_helpers': 1, 'definition_checks': 1, 'Prop_axiom_credit': 0,
    'historical_substitutions': len(historical_substitutions), 'normal_Source_changed': False}))
