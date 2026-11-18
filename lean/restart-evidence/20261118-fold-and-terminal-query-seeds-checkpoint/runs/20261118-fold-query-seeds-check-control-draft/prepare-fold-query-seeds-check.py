from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-fold-query-seeds-check-control-draft'
WORK = BASE / '20261118-fold-query-seeds-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root reviews and copies this preparer into NEW Work61.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-fold-query-seeds-check.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


def records(manifest):
    files = manifest['files']
    return files.items() if isinstance(files, dict) else [(item.get('file', item.get('path')), item) for item in files]


def bind_packet(packet, expected_manifest):
    manifest = json.loads(verify(packet / 'MANIFEST.json', expected_manifest))
    for name, record in records(manifest):
        verify(packet / name, record)
    return manifest


manifest = json.loads((CONTROL / 'MANIFEST.json').read_text())
assert manifest['status'] == 'FROZEN PRIVATE CHECK CONTROLLER / NOT EXECUTED'
for name, record in records(manifest):
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
selection = json.loads((CONTROL / 'SELECTION.json').read_text())
assert selection['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert selection['work'] == WORK.name
assert selection['runtime'] == '20261118-fold-query-seeds-check'
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Use a new runtime. Preserve every earlier proof attempt.'
assert selection['source_files'] == 6284
assert re.fullmatch(r'[0-9a-f]{40}', selection['source_commit'])
assert re.fullmatch(r'[0-9a-f]{40}', selection['verified_prior_checkpoint_commit'])
assert selection['expected_checks'] == len(selection['components']) == 1
assert selection['expected_public_axiom_reports'] == 2
assert selection['expected_explicit_private_axiom_reports'] == selection['expected_declaration_checks'] == 0
assert selection['new_private_helpers_transitive'] == selection['new_definitions'] == 0
assert selection['prior_checkpoint_push_required_for_private_check']
assert selection['prior_checkpoint_push_required_before_normal_Source_staging']
for name, record in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
prior = BASE / selection['prior_work']
publication = BASE / selection['prior_publication_runtime']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
receipt = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
checked = json.loads((publication / 'checked.json').read_text())
assert commit['source_commit'] == selection['source_commit']
assert commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert commit['publication_actual_session'] == receipt['actual_session'] == actual['actual_session'] == selection['prior_publication_actual_session'] == 88140
assert receipt['actual_terminal'] and actual['actual_terminal']
assert receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert receipt['runtime'] == actual['runtime'] == selection['prior_publication_runtime']
assert checked == json.loads((publication / 'results.json').read_text())
assert checked['checks'] == receipt['checks']
assert SHA((publication / 'checked.json').read_bytes()) == receipt['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == receipt['source_pins_sha256']
assert [item['total_axiom_reports'] for item in checked['checks']] == [738, 3, 333, 738, 738]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms']
    and item['declaration_checks'] == 0 for item in checked['checks'])
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert receipt['source_files'] == 6284 and receipt['direct_audit_imports'] == 5284
assert receipt['audited_theorems'] == commit['audited_theorems'] == 100233
assert receipt['pins_independently_reverified'] == 8803
assert receipt['actual_incoming_source_Seeds_transition_checked'] and receipt['actual_dispatch_source_Seeds_transition_checked']
assert not receipt['joint_finite_completion_proved']
publication_pins = json.loads((publication / 'source-pins.json').read_text())
assert len(publication_pins) == receipt['pins_independently_reverified']
for name, digest in publication_pins.items():
    verify(ROOT / name, digest)
push = json.loads((ROOT / selection['prior_push_verified_receipt']).read_text())
assert push['source_commit'] == selection['source_commit']
assert push['checkpoint_commit'] == push['remote_commit'] == selection['verified_prior_checkpoint_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
assert push['normal_Source_files'] == 6284

# Root may commit documentation after Source60. Source and toolchain must stay exact.
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', selection['source_commit'], 'HEAD'], cwd=ROOT, check=True)
changes = subprocess.check_output(['git', 'diff', '--name-only', selection['source_commit'], 'HEAD'], cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md'] or name.startswith('lean/restart-evidence/') for name in changes), changes
subprocess.run(['git', 'diff', '--quiet', selection['source_commit'], '--', 'lean/MicroCFTA',
    'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / selection['source_baseline']).read_text())
assert baseline['source_commit'] == selection['source_commit'] and baseline['source_files'] == 6284
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6284 and {str(path.relative_to(ROOT)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert publication_pins[name] == record['sha256'], name
item = selection['components'][0]
assert item['module'] == 'SourcePruningEnumerationSharedTerminalFoldQueryEvents'
assert selection['compile_order'] == [item['module']]
packet = BASE / item['packet']
bind_packet(packet, item['manifest_sha256'])
for record in json.loads((packet / 'SOURCE-PINS.json').read_text())['files']:
    verify(ROOT / record['file'], record)
raw = verify(packet / item['source'], {'bytes': item['raw_bytes'], 'sha256': item['raw_sha256']})
raw_packet = BASE / item['raw_base_packet']
bind_packet(raw_packet, item['raw_base_manifest_sha256'])
for record in json.loads((raw_packet / 'SOURCE-PINS.json').read_text())['files']:
    verify(ROOT / record['file'], record)
raw_base = verify(raw_packet / item['source'], {'bytes': item['raw_base_bytes'], 'sha256': item['raw_base_sha256']})
before = verify(ROOT / item['owner_source'], {'bytes': item['owner_bytes'], 'sha256': item['owner_sha256']})
assert before == verify(CONTROL / 'OWNER-BEFORE.lean.txt', item['owner_sha256'])
assert len(before) == 36968 and raw_base[66:66 + 36968] == before
imports = (raw_packet / 'IMPORTS.lean.txt').read_bytes()
assert imports == b'import MicroCFTA.SourcePruningEnumerationSharedIncomingQuerySeeds\n' and len(imports) == 66
raw_append = (raw_packet / 'APPEND.lean.txt').read_bytes()
assert raw_base == imports + before + raw_append and len(raw_base) == 47686
appended = verify(packet / item['append'], item['append_sha256'])
assert raw == raw_base + appended and len(raw) == 60925
assembly = json.loads(verify(packet / item['assembly'], item['assembly_sha256']))
assert assembly['base_bytes'] == 47686 and assembly['base_entire_prefix_offset'] == 0 and assembly['new_imports'] == 0
raw_header = verify(raw_packet / 'FIRST-HEADER.lean.txt', item['raw_header_sha256'])
header = verify(packet / item['header'], item['header_sha256'])
assert raw_header == (CONTROL / 'RAW-FIRST-HEADER.lean.txt').read_bytes()
assert header == (CONTROL / 'FIRST-HEADER.lean.txt').read_bytes()
assert raw_append.count(raw_header.rstrip()) == appended.count(header.rstrip()) == 1
assert re.findall(r'^theorem (\w+)', raw_append.decode(), re.M) == ['rawFold_original_source_observe_preserves_seeds']
assert re.findall(r'^theorem (\w+)', appended.decode(), re.M) == ['fold_original_source_observe_preserves_seeds']
for new_part in [raw_append, appended]:
    assert not re.findall(rb'^(?:private theorem |(?:private )?(?:def|inductive|structure) )', new_part, re.M)
    assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', new_part)
assert not re.search(rb'\b(?:sorry|axiom)\b', raw)
probe = verify(packet / item['probe'], item['probe_sha256'])
assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['public_qnames']
assert probe.count(b'#print axioms ') == item['expected_axiom_reports'] == 2 and b'#check ' not in probe
assert b'#print axioms ' not in raw and b'#check ' not in raw
# The dispatch dependency is now published Source60. Do not compile it again here.
dependency_packet = BASE / item['normal_dependency_packet']
bind_packet(dependency_packet, item['normal_dependency_manifest_sha256'])
dependency_source = ROOT / 'lean/MicroCFTA' / (item['normal_dependency_module'] + '.lean')
assert verify(dependency_source, item['normal_dependency_source_sha256']) == (dependency_packet / dependency_source.name).read_bytes()

normal_objects = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
paths = {path.stem: path for path in sources}
active, seen, order, graph = [], set(), [], {}


def visit(name):
    assert name not in active, 'Import cycle: ' + repr(active + [name])
    if name in seen:
        return
    active.append(name)
    data = raw.decode() if name == item['module'] else paths[name].read_text()
    graph[name] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', data, re.M)
    for dependency in graph[name]:
        assert dependency in paths, dependency
        visit(dependency)
    active.pop()
    seen.add(name)
    order.append(name)


visit(item['module'])
topological = json.loads((CONTROL / 'TOPOLOGICAL-ORDER.json').read_text())
assert graph == topological['direct_imports'] and order == topological['full_transitive_order']
assert len(order) == 2347 and len(seen - {item['module']}) == 2346
for name in seen - {item['module']}:
    assert (normal_objects / (name + '.olean')).is_file(), name
assert item['normal_dependency_module'] in seen
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((CONTROL / name).read_text())
# Root creates the fresh runtime only after every read-only gate passes.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-fold-query-seeds-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for obj in sorted(normal_objects.glob('*.olean')):
    if obj.stem != item['module']:
        (objects / 'MicroCFTA' / obj.name).symlink_to(obj)
        linked.append(obj.name)
assert item['module'] + '.olean' not in linked
assert item['normal_dependency_module'] + '.olean' in linked
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'linked_unchanged_modules': linked,
    'excluded_candidate_modules': [item['module']], 'candidate_output_links_created': False,
    'normal_dependency_modules': 2346, 'cache_data_copied': False}, indent=2) + '\n')
fixture = runtime / 'source/MicroCFTA' / item['source']
fixture.parent.mkdir(parents=True)
fixture.write_bytes(raw + b'\n' + probe)
bound.add(fixture)
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
(runtime / 'NORMAL-STAGING-GATE.json').write_text(json.dumps({
    'source_commit': selection['source_commit'], 'prior_Work60_push_receipt': selection['prior_push_verified_receipt'],
    'checkpoint_commit': push['checkpoint_commit'], 'private_check_requires_checkpoint_push': True,
    'normal_Source_staging_requires_checkpoint_push': True, 'normal_Source_staging_executed_by_this_controller': False}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 1,
    'expected_public_reports': 2, 'explicit_private_reports': 0, 'new_private_helpers': 0, 'definition_checks': 0,
    'entire_raw_semantic_prefix_exact': True, 'old_owner_bytes': 36968, 'old_owner_offset': 66,
    'normal_Source_changed': False, 'prior_checkpoint_push_required_before_private_check': True}))
