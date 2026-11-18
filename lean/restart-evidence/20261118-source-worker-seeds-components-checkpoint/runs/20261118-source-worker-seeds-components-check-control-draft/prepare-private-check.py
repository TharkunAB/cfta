from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-source-worker-seeds-components-check-control-draft'
WORK = BASE / '20261118-source-worker-seeds-components-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root must review and copy this preparer into the new Work directory.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-private-check.py').read_bytes()
selection = json.loads((CONTROL / 'SELECTION.json').read_text())
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Preserve every earlier attempt. Use a fresh runtime.'
SHA = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    assert SHA(data) == digest, str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


def file_records(manifest):
    entries = manifest['files']
    if isinstance(entries, dict):
        return entries.items()
    return [(item.get('file', item.get('path')), item) for item in entries]


for name, record in file_records(json.loads((CONTROL / 'MANIFEST.json').read_text())):
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
assert selection['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert selection['source_commit'] == 'fc345af6e51dd1e813fed83423f25c3228b78874'
assert selection['source_files'] == 6279
assert selection['expected_checks'] == len(selection['components']) == 3
assert selection['expected_public_axiom_reports'] == 5
assert selection['expected_explicit_private_axiom_reports'] == 0
assert selection['expected_declaration_checks'] == selection['new_Prop_definitions'] == 0
assert selection['new_private_helpers_transitive'] == 2
assert not selection['prior_checkpoint_push_required_for_private_check']
assert selection['prior_checkpoint_push_required_before_normal_Source_staging']
for name, record in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
prior = BASE / selection['prior_work']
publication = BASE / selection['prior_publication_runtime']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
verified = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
checked = json.loads((publication / 'checked.json').read_text())
assert commit['source_commit'] == selection['source_commit']
assert commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert commit['publication_actual_session'] == verified['actual_session'] == actual['actual_session'] == 73094
assert verified['actual_terminal'] and actual['actual_terminal']
assert verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert verified['checks'] == checked['checks']
assert checked == json.loads((publication / 'results.json').read_text())
assert SHA((publication / 'checked.json').read_bytes()) == verified['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == verified['source_pins_sha256']
assert [item['name'] for item in checked['checks']] == ['public-build',
    'strict-new-components-and-prior-bindings', 'independent-imports', 'audit-build', 'audit-strict']
assert [item['total_axiom_reports'] for item in checked['checks']] == [726, 2, 321, 726, 726]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['declaration_checks'] == 0 for item in checked['checks'])
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert verified['source_files'] == 6279 and verified['direct_audit_imports'] == 5279
assert verified['audited_theorems'] == commit['audited_theorems'] == 100191
assert verified['pins_independently_reverified'] == 7859
assert not verified['joint_finite_completion_proved']

# A later checkpoint may change only the three status documents and frozen evidence.
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', selection['source_commit'], 'HEAD'], cwd=ROOT, check=True)
changed = subprocess.check_output(['git', 'diff', '--name-only', selection['source_commit'], 'HEAD'], cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']
    or name.startswith('lean/restart-evidence/') for name in changed), changed
subprocess.run(['git', 'diff', '--quiet', selection['source_commit'], 'HEAD', '--',
    'lean/MicroCFTA', 'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / 'SOURCE-BASELINE-PINS.json').read_text())
assert baseline['source_commit'] == selection['source_commit'] and baseline['source_files'] == 6279
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert {str(path.relative_to(ROOT)) for path in sources} == set(baseline['sources']) and len(sources) == 6279
publication_pins = json.loads((publication / 'source-pins.json').read_text())
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert publication_pins[name] == record['sha256'], name

seen_manifests = set()


def verify_packet(path, digest, direct_source_pins=True):
    verify(path, digest)
    if path in seen_manifests:
        return
    seen_manifests.add(path)
    packet = path.parent
    for name, record in file_records(json.loads(path.read_text())):
        verify(packet / name, record)
    if not direct_source_pins:
        return
    pin_path = packet / 'SOURCE-PINS.json'
    if not pin_path.exists():
        return
    bound.add(pin_path)
    pin_data = json.loads(pin_path.read_text())
    if 'pins' in pin_data:
        records = pin_data['pins'].items()
    elif 'files' in pin_data:
        records = [(item['file'], item) for item in pin_data['files']]
    else:
        records = pin_data.items()
    for name, record in records:
        target = ROOT / name
        verify(target, record)
        if target.name == 'MANIFEST.json':
            verify_packet(target, record['sha256'] if isinstance(record, dict) else record, False)


normal_objects = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
candidate_names = set(selection['compile_order'])
assert len(candidate_names) == 3
assert selection['compile_order'] == [item['module'] for item in selection['components']]
raw_sources = {}
for item in selection['components']:
    packet = BASE / item['packet']
    verify_packet(packet / 'MANIFEST.json', item['manifest_sha256'])
    raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    if item['kind'] == 'existing_owner_import_and_EOF':
        before = verify(ROOT / item['owner_source'], {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
        assert before == verify(CONTROL / 'OWNER-BEFORE.lean.txt', item['owner_sha256']) and len(before) == 23529
        imports = verify(packet / item['imports'], item['imports_sha256'])
        appended = verify(packet / item['append'], item['append_sha256'])
        assembly = json.loads(verify(packet / item['assembly'], item['assembly_sha256']))
        assert assembly['old_owner_offset'] == len(imports) == 61
        assert assembly['owner_sha256'] == SHA(before)
        assert raw == imports + before + appended
        theorem_source = appended
    else:
        assert item['kind'] == 'new_module'
        assert not (ROOT / 'lean/MicroCFTA' / (item['module'] + '.lean')).exists()
        theorem_source = raw
    for header in item['headers']:
        first = verify(packet / header['file'], header['sha256'])
        assert theorem_source.count(first) == 1, header['file']
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert not re.search(rb'\b(?:sorry|axiom)\b', raw)
    assert not re.search(rb'set_option (?:maxHeartbeats|maxRecDepth|linter\.)', theorem_source)
    probe = verify(packet / item['probe'], item['probe_sha256'])
    qnames = re.findall(r'^#print axioms (\S+)', probe.decode(), re.M)
    assert qnames == item['public_qnames'] and len(qnames) == item['expected_axiom_reports']
    assert probe.count(b'#check ') == item['expected_declaration_checks'] == 0
    assert re.findall(r'^theorem (\w+)', theorem_source.decode(), re.M) == [x.rsplit('.', 1)[1] for x in qnames]
    assert len(re.findall(r'^private theorem (\w+)', theorem_source.decode(), re.M)) == item['new_private_helpers_transitive']
    assert not re.findall(r'^(?:private )?(?:def|inductive|structure) ', theorem_source.decode(), re.M)
    raw_sources[item['module']] = raw
assert sum(x['expected_axiom_reports'] for x in selection['components']) == 5
assert sum(x['new_private_helpers_transitive'] for x in selection['components']) == 2

# The repaired incoming basename must retain the old resource owner as a normal dependency.
assert 'SourcePruningEnumerationSharedIncomingQueryResources' not in candidate_names
assert (ROOT / 'lean/MicroCFTA/SourcePruningEnumerationSharedIncomingQueryResources.lean').is_file()
compatibility = json.loads((CONTROL / 'INCOMING-FILENAME-COMPARISON.json').read_text())
original = BASE / compatibility['original_packet']
selected = BASE / compatibility['selected_packet']
assert verify(original / 'MANIFEST.json', compatibility['original_manifest_sha256'])
assert verify(selected / 'MANIFEST.json', compatibility['selected_manifest_sha256'])
assert verify(original / compatibility['original_source'], compatibility['raw_sha256']) == verify(selected / compatibility['selected_source'], compatibility['raw_sha256'])
assert verify(original / 'FIRST-HEADER.lean.txt', compatibility['header_sha256']) == verify(selected / 'FIRST-HEADER.lean.txt', compatibility['header_sha256'])

# Derive the complete import order from actual selected source text, not cached objects.
module_files = {path.stem: path for path in sources}
graph = {name: re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', path.read_text(), re.M)
    for name, path in module_files.items()}
for name, raw in raw_sources.items():
    graph[name] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', raw.decode(), re.M)
order = []
active = []
visited = set()


def visit(name):
    assert name not in active, 'Import cycle: ' + repr(active + [name])
    if name in visited:
        return
    active.append(name)
    for dependency in graph[name]:
        assert dependency in graph, (name, dependency)
        visit(dependency)
    active.pop()
    visited.add(name)
    order.append(name)


for name in selection['compile_order']:
    visit(name)
topological = json.loads((CONTROL / 'TOPOLOGICAL-ORDER.json').read_text())
assert order == topological['full_transitive_order']
assert {name: graph[name] for name in order} == topological['direct_imports']
assert [name for name in order if name in candidate_names] == selection['compile_order']
assert len(order) == 2381 and len(visited - candidate_names) == 2378
for name in visited - candidate_names:
    assert (normal_objects / (name + '.olean')).is_file(), name
for filename in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((CONTROL / filename).read_text())

# Only Root executes the following materialization after all read-only gates pass.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-source-worker-seeds-components-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for dependency in sorted(normal_objects.glob('*.olean')):
    if dependency.stem not in candidate_names:
        (objects / 'MicroCFTA' / dependency.name).symlink_to(dependency)
        linked.append(dependency.name)
assert 'SourcePruningEnumerationSharedIncomingQueryResources.olean' in linked
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({
    'normal_objects': str(normal_objects), 'linked_unchanged_modules': linked,
    'excluded_candidate_modules': sorted(candidate_names),
    'verified_transitive_modules': len(order), 'verified_transitive_normal_modules': 2378,
    'candidate_output_links_created': False, 'cache_data_copied': False,
    'original_incoming_resource_owner_retained': True}, indent=2) + '\n')
source_root = runtime / 'source/MicroCFTA'
source_root.mkdir(parents=True)
for item in selection['components']:
    path = source_root / (item['module'] + '.lean')
    path.write_bytes(raw_sources[item['module']] + b'\n' + (BASE / item['packet'] / item['probe']).read_bytes())
    bound.add(path)
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2, sort_keys=True) + '\n')
(runtime / 'NORMAL-STAGING-GATE.json').write_text(json.dumps({
    'source_commit': selection['source_commit'],
    'required_Work57_push_receipt': selection['prior_push_verified_receipt'],
    'checkpoint_commit': 'READ DYNAMICALLY FROM FINAL Work57/PUSH-VERIFIED.json',
    'private_check_can_precede_prior_checkpoint_push': True,
    'normal_Source_staging_requires_prior_checkpoint_push': True,
    'normal_Source_staging_executed_by_this_controller': False}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 3,
    'expected_public_reports': 5, 'expected_explicit_private_reports': 0,
    'new_private_helpers_transitive': 2, 'new_Prop_definitions': 0,
    'compile_order': selection['compile_order'], 'transitive_source_modules': 2381,
    'normal_Source_changed': False, 'published': False,
    'prior_checkpoint_push_required_before_normal_Source_staging': True}))
