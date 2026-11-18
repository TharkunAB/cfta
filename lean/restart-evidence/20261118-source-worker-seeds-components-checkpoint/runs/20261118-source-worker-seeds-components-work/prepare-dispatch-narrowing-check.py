from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261118-source-worker-dispatch-narrowing-check-control-draft'
work = base / '20261118-source-worker-seeds-components-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller into the new Work directory.'
assert Path(__file__).read_bytes() == (control / 'prepare-dispatch-narrowing-check.py').read_bytes()
selection = json.loads((control / 'SELECTION.json').read_text())
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


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
bound.add(control / 'MANIFEST.json')
assert selection['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert selection['source_commit'] == 'fc345af6e51dd1e813fed83423f25c3228b78874'
assert selection['source_files'] == 6279
assert len(selection['components']) == selection['expected_checks'] == 2
assert selection['compile_order'] == [item['module'] for item in selection['components']]
assert selection['compile_order'] == ['SourcePruningEnumerationSelectedPrefixNarrowNoNewMu', 'SourcePruningEnumerationSharedDispatchQueryEventResources']
assert selection['expected_axiom_reports'] == 2 and selection['expected_declaration_checks'] == 0
for name, record in json.loads((control / 'RECEIPT-PINS.json').read_text()).items():
    verify(root / name, record)
prior = base / selection['prior_work']
publication_runtime = base / selection['prior_publication_runtime']
source_commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
publication = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual_publication = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
checked = json.loads((publication_runtime / 'checked.json').read_text())
assert source_commit['source_commit'] == selection['source_commit']
assert source_commit['actual_terminal'] and source_commit['actual_terminal_exit'] == 0
assert source_commit['private_actual_session'] == selection['prior_source_private_session'] == 15994
assert source_commit['publication_actual_session'] == publication['actual_session'] == 73094
assert actual_publication['actual_session'] == 73094 and actual_publication['actual_terminal']
assert actual_publication['actual_terminal_exit'] == 0
assert publication['actual_terminal'] and publication['actual_terminal_exit'] == 0
assert publication['source_files'] == 6279 and publication['direct_audit_imports'] == 5279
assert publication['pins_independently_reverified'] == 7859
assert publication['audited_theorems'] == source_commit['audited_theorems'] == 100191
assert [item['total_axiom_reports'] for item in publication['checks']] == [726, 2, 321, 726, 726]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] for item in publication['checks'])
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert checked['checks'] == publication['checks']
assert not publication['joint_finite_completion_proved']
assert sha((publication_runtime / 'source-pins.json').read_bytes()) == publication['source_pins_sha256']
assert sha((publication_runtime / 'checked.json').read_bytes()) == publication['checked_sha256']
push = json.loads((root / selection['prior_push_verified_receipt']).read_text())
assert push['source_commit'] == selection['source_commit']
assert push['checkpoint_commit'] == push['remote_commit'] == selection['expected_prior_checkpoint']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
prior_subset = json.loads((work / selection['prior_successful_subset_receipt']).read_text())
assert prior_subset['actual_session'] == selection['prior_successful_subset_actual_session'] == 23742
assert prior_subset['actual_terminal'] and prior_subset['actual_terminal_exit'] == 0
assert [item['total_axiom_reports'] for item in prior_subset['checks']] == [1, 3, 1]

# Documentation-only commits may advance HEAD. Source and toolchain stay exact.
subprocess.run(['git', 'merge-base', '--is-ancestor', selection['source_commit'], 'HEAD'], cwd=root, check=True)
subprocess.run(['git', 'diff', '--quiet', selection['source_commit'], 'HEAD', '--',
    'lean/MicroCFTA', 'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'],
    cwd=root, check=True)
baseline = json.loads((control / selection['source_baseline']).read_text())
assert baseline['source_commit'] == selection['source_commit'] and baseline['source_files'] == 6279
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6279
assert {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
publication_pins = json.loads((publication_runtime / 'source-pins.json').read_text())
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(root / name, record)
    assert publication_pins[name] == record['sha256'], name

seen_manifests = set()
checked_direct_pin_manifests = set()


def verify_packet(path, digest, direct_pins=False):
    verify(path, digest)
    packet = path.parent
    if path not in seen_manifests:
        seen_manifests.add(path)
        manifest = json.loads(path.read_text())
        files = manifest['files']
        entries = files.items() if isinstance(files, dict) else [(item['file'], item) for item in files]
        for name, record in entries:
            verify(packet / name, record)
    if not direct_pins or path in checked_direct_pin_manifests:
        return
    checked_direct_pin_manifests.add(path)
    for filename in ['SOURCE-PINS.json', 'ADDITIONAL-SOURCE-PINS.json', 'DEPENDENCY-PINS.json']:
        pin_path = packet / filename
        if not pin_path.exists():
            continue
        bound.add(pin_path)
        pin_data = json.loads(pin_path.read_text())
        if 'files' in pin_data:
            entries = [(item['file'], item) for item in pin_data['files']]
        elif 'pins' in pin_data:
            entries = pin_data['pins'].items()
        else:
            entries = pin_data.items()
        for name, record in entries:
            target = root / name
            verify(target, record)
            if target.name == 'MANIFEST.json':
                verify_packet(target, record['sha256'] if isinstance(record, dict) else record)


normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
candidate_names = set(selection['compile_order'])
normal_imports = set()
raw_sources = {}
for item in selection['components']:
    packet = base / item['packet']
    verify_packet(packet / 'MANIFEST.json', item['manifest_sha256'], direct_pins=True)
    raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    assert item['kind'] == 'new_module'
    target = root / 'lean/MicroCFTA' / item['source']
    assert not target.exists() and not target.is_symlink(), str(target)
    theorem_source = raw
    verify(packet / item['assembly'], item['assembly_sha256'])
    first = verify(packet / item['header'], item['header_sha256'])
    first_line = first.splitlines()[0]
    start = theorem_source.index(first_line)
    end = theorem_source.index(b':= by', start)
    assert theorem_source[start:end].rstrip() == first.rstrip()
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert b'set_option maxHeartbeats' not in theorem_source and b'set_option maxRecDepth' not in theorem_source
    assert b'set_option linter' not in theorem_source
    probe = verify(packet / item['probe'], item['probe_sha256'])
    qnames = re.findall(r'^#print axioms (\S+)', probe.decode(), re.M)
    assert qnames == item['public_qnames'] and len(qnames) == item['expected_axiom_reports'] == 1
    assert probe.count(b'#check ') == item['expected_declaration_checks'] == 0
    assert re.findall(r'^theorem (\w+)', theorem_source.decode(), re.M) == [qnames[0].rsplit('.', 1)[1]]
    assert len(re.findall(r'^private theorem (\w+)', theorem_source.decode(), re.M)) == item['new_private_theorems']
    assert not re.findall(r'^(?:private )?def ', theorem_source.decode(), re.M)
    for name in re.findall(rb'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', raw, re.M):
        module = name.decode()
        if module not in candidate_names:
            assert (normal_objects / (module + '.olean')).is_file(), module
            normal_imports.add(module)
    raw_sources[item['module']] = raw + b'\n' + probe
assert sum(item['new_private_theorems'] for item in selection['components']) == 5
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((control / name).read_text())

dag_path = control / 'IMPORT-DAG.json'
dag = json.loads(dag_path.read_text())
bound.add(dag_path)
edges = {}
visiting = set()
visited = set()
ordered = []

def walk(module):
    if module in visited:
        return
    assert module not in visiting, ('import cycle', module)
    visiting.add(module)
    if module in candidate_names:
        item = next(item for item in selection['components'] if item['module'] == module)
        data = (base / item['packet'] / item['source']).read_text()
    else:
        path = root / 'lean/MicroCFTA' / (module + '.lean')
        data = verify(path, baseline['sources'][str(path.relative_to(root))]).decode()
        assert (normal_objects / (module + '.olean')).is_file(), module
    edges[module] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', data, re.M)
    for imported in edges[module]:
        walk(imported)
    visiting.remove(module)
    visited.add(module)
    ordered.append(module)

for module in selection['compile_order']:
    walk(module)
assert edges == dag['edges']
assert [module for module in ordered if module in candidate_names] == selection['compile_order']
assert set(dag['normal_transitive_modules']) == visited - candidate_names
assert dag['normal_transitive_count'] == len(visited - candidate_names) == 2257

# Root executes this phase only after every preflight above has passed.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-dispatch-narrowing-check-'))
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
selected['control_manifest_sha256'] = sha((control / 'MANIFEST.json').read_bytes())
(runtime / 'selection.json').write_text(json.dumps(selected, indent=2, sort_keys=True) + '\n')
(runtime / 'SUBSET-SCOPE.json').write_text(json.dumps({
    'same_Work58_existing_attempts_retained': True,
    'prior_subset_receipt': selection['prior_successful_subset_receipt'],
    'prior_subset_actual_session': 23742,
    'prior_subset_report_credit_included_here': False,
    'normal_Source_staging_executed': False,
    'both_normal_module_filenames_absent': True,
    'current_subset_public_reports': 2, 'current_subset_private_helpers_transitive': 5,
    'all_worker_query_admissions_proved': False, 'joint_finite_completion_proved': False,
}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({
    str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound)
}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 2,
    'actual_new_public_reports_expected': 2, 'definition_checks': 0, 'new_private_explicit_reports': 0,
    'new_private_helpers': 5, 'new_prop_definitions': 0,
    'fresh_credit_for_old_owner_theorems': 0,
    'compile_order': selection['compile_order'], 'normal_source_changed': False,
    'current_subset_only': True}))
