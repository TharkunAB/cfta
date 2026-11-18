from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-actual-source-child-query-seeds-check-control-draft'
WORK = BASE / '20261118-actual-source-child-query-seeds-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root reviews and copies this preparer into NEW Work64.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-actual-source-child-query-seeds-check.py').read_bytes()
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
assert selection['runtime'] == '20261118-actual-source-child-query-seeds-check'
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Use a new runtime. Preserve every earlier proof attempt.'
assert selection['source_files'] == 6286
assert re.fullmatch(r'[0-9a-f]{40}', selection['source_commit'])
assert re.fullmatch(r'[0-9a-f]{40}', selection['verified_prior_checkpoint_commit'])
assert selection['expected_checks'] == len(selection['components']) == 1
assert selection['expected_public_axiom_reports'] == 0
assert selection['expected_explicit_private_axiom_reports'] == 1
assert selection['expected_declaration_checks'] == 0
assert selection['new_private_helpers_transitive'] == 0
assert selection['new_definitions'] == 0 and selection['definition_axiom_credit'] == 0
assert selection['new_private_theorems'] == 1
assert selection['root_math_review_confirmed']
assert selection['prior_checkpoint_push_required_for_private_check']
assert selection['prior_checkpoint_push_required_before_normal_Source_staging']
for name, record in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
review = json.loads((ROOT / selection['root_math_review_receipt']).read_text())
assert review['Root_entire_append_and_FIRST_and_proof_read'] and not review['semantic_concerns_found']
assert review['candidate_manifest'] == selection['components'][0]['manifest_sha256']
assert review['FIRST_sha256'] == selection['components'][0]['headers']['FIRST-HEADER.lean.txt']
assert review['source_baseline'] == selection['source_commit']
assert review['prior_checkpoint'] == selection['verified_prior_checkpoint_commit']
assert review['expected_public_reports'] == 0 and review['expected_explicit_private_reports'] == 1
prior = BASE / selection['prior_work']
publication = BASE / selection['prior_publication_runtime']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
receipt = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
checked = json.loads((publication / 'checked.json').read_text())
assert commit['source_commit'] == selection['source_commit']
assert commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert commit['publication_actual_session'] == receipt['actual_session'] == actual['actual_session'] == selection['prior_publication_actual_session']
assert receipt['actual_terminal'] and actual['actual_terminal']
assert receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert receipt['runtime'] == actual['runtime'] == selection['prior_publication_runtime']
assert checked == json.loads((publication / 'results.json').read_text())
assert checked['checks'] == receipt['checks']
assert SHA((publication / 'checked.json').read_bytes()) == receipt['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == receipt['source_pins_sha256']
assert [item['total_axiom_reports'] for item in checked['checks']] == [744, 1, 339, 744, 744]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in checked['checks'])
assert [item['declaration_checks'] for item in checked['checks']] == [0, 1, 0, 0, 0]
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert receipt['source_files'] == 6286 and receipt['direct_audit_imports'] == 5286
assert receipt['audited_theorems'] == commit['audited_theorems'] == selection['prior_publication_audited_theorems']
assert receipt['pins_independently_reverified'] == selection['prior_publication_pins_reverified']
assert receipt['indexed_query_origin_from_one_operation_list']
assert receipt['all_operation_fields_and_native_run_result_retained']
assert receipt['definition_checks'] == 1 and receipt['definition_axiom_credit'] == 0
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
assert push['normal_Source_files'] == 6286

# Root may commit documentation after Source63. Source and toolchain must stay exact.
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', selection['source_commit'], 'HEAD'], cwd=ROOT, check=True)
changes = subprocess.check_output(['git', 'diff', '--name-only', selection['source_commit'], 'HEAD'], cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md'] or name.startswith('lean/restart-evidence/') for name in changes), changes
subprocess.run(['git', 'diff', '--quiet', selection['source_commit'], '--', 'lean/MicroCFTA',
    'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / selection['source_baseline']).read_text())
assert baseline['source_commit'] == selection['source_commit'] and baseline['source_files'] == 6286
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6286 and {str(path.relative_to(ROOT)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert publication_pins[name] == record['sha256'], name
item = selection['components'][0]
assert item['module'] == 'SourcePruningEnumerationSharedEagerReservation'
assert selection['compile_order'] == [item['module']]
packet = BASE / item['packet']
bind_packet(packet, item['manifest_sha256'])
for name, record in json.loads((packet / 'SOURCE-PINS.json').read_text())['files'].items():
    verify(ROOT / name, record)
raw = verify(packet / item['source'], {'bytes': item['raw_bytes'], 'sha256': item['raw_sha256']})
old_owner = verify(ROOT / item['old_owner_source'], {'bytes': item['old_owner_bytes'], 'sha256': item['old_owner_sha256']})
assert verify(packet / 'OWNER-BEFORE.lean.txt', item['old_owner_sha256']) == old_owner
imports = verify(packet / 'IMPORTS.lean.txt', item['imports_sha256'])
append = verify(packet / 'APPEND.lean.txt', item['append_sha256'])
assert len(imports) == item['old_owner_offset'] == 72
assert imports == b'import MicroCFTA.SourcePruningEnumerationSharedChildDispatchQueryEvents\n'
assert raw == imports + old_owner + b'\n' + append
assert raw[len(imports):len(imports)+len(old_owner)] == old_owner
for name, digest in item['headers'].items():
    header = verify(packet / name, digest)
    assert append.count(header.rstrip()) == raw.count(header.rstrip()) == 1
assert re.findall(r'^private theorem (\w+)', append.decode(), re.M) == ['actual_source_child_query_resources_and_seeds']
assert not re.findall(r'^(?:theorem |(?:private )?(?:noncomputable )?(?:def|inductive|structure) )', append.decode(), re.M)
assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', append)
assert not re.search(rb'\b(?:sorry|axiom)\b', append)
probe = verify(packet / item['probe'], item['probe_sha256'])
assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['private_qnames']
assert probe.count(b'#print axioms ') == item['expected_axiom_reports'] == 1
assert b'#check ' not in probe and item['expected_declaration_checks'] == 0
assert b'#print axioms ' not in raw and b'#check ' not in raw
for module, digest in item['normal_dependencies'].items():
    verify(ROOT / 'lean/MicroCFTA' / (module + '.lean'), digest)

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
assert len(order) == 2864 and len(seen - {item['module']}) == 2863
for name in seen - {item['module']}:
    assert (normal_objects / (name + '.olean')).is_file(), name
assert set(item['normal_dependencies']).issubset(seen)
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((CONTROL / name).read_text())
# Root creates the fresh runtime only after every read-only gate passes.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-actual-source-child-query-seeds-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for obj in sorted(normal_objects.glob('*.olean')):
    if obj.stem != item['module']:
        (objects / 'MicroCFTA' / obj.name).symlink_to(obj)
        linked.append(obj.name)
assert item['module'] + '.olean' not in linked
assert all(name + '.olean' in linked for name in item['normal_dependencies'])
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'linked_unchanged_modules': linked,
    'excluded_candidate_modules': [item['module']], 'candidate_output_links_created': False,
    'normal_dependency_modules': 2863, 'cache_data_copied': False}, indent=2) + '\n')
fixture = runtime / 'source/MicroCFTA' / item['source']
fixture.parent.mkdir(parents=True)
fixture.write_bytes(raw + b'\n' + probe)
bound.add(fixture)
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
(runtime / 'NORMAL-STAGING-GATE.json').write_text(json.dumps({
    'source_commit': selection['source_commit'], 'prior_Work63_push_receipt': selection['prior_push_verified_receipt'],
    'checkpoint_commit': push['checkpoint_commit'], 'private_check_requires_checkpoint_push': True,
    'normal_Source_staging_requires_checkpoint_push': True, 'normal_Source_staging_executed_by_this_controller': False}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 1,
    'expected_public_reports': 0, 'explicit_private_reports': 1, 'new_private_helpers': 1, 'definition_checks': 0, 'definition_axiom_credit': 0,
    'new_definitions': 0,
    'normal_Source_changed': False, 'prior_checkpoint_push_required_before_private_check': True}))
