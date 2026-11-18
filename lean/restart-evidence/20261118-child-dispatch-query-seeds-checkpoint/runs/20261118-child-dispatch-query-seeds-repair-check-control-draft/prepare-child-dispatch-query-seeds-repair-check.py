from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-child-dispatch-query-seeds-repair-check-control-draft'
WORK = BASE / '20261118-child-dispatch-query-seeds-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root reviews and copies this preparer into NEW Work62.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-child-dispatch-query-seeds-repair-check.py').read_bytes()
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
assert selection['runtime'] == '20261118-child-dispatch-query-seeds-repair-check'
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Use a new runtime. Preserve every earlier proof attempt.'
assert selection['source_files'] == 6284
assert re.fullmatch(r'[0-9a-f]{40}', selection['source_commit'])
assert re.fullmatch(r'[0-9a-f]{40}', selection['verified_prior_checkpoint_commit'])
assert selection['expected_checks'] == len(selection['components']) == 1
assert selection['expected_public_axiom_reports'] == 2
assert selection['expected_explicit_private_axiom_reports'] == 0
assert selection['expected_declaration_checks'] == 1
assert selection['new_private_helpers_transitive'] == 0
assert selection['new_definitions'] == 1 and selection['definition_axiom_credit'] == 0
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
assert commit['publication_actual_session'] == receipt['actual_session'] == actual['actual_session'] == selection['prior_publication_actual_session']
assert receipt['actual_terminal'] and actual['actual_terminal']
assert receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert receipt['runtime'] == actual['runtime'] == selection['prior_publication_runtime']
assert checked == json.loads((publication / 'results.json').read_text())
assert checked['checks'] == receipt['checks']
assert SHA((publication / 'checked.json').read_bytes()) == receipt['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == receipt['source_pins_sha256']
assert [item['total_axiom_reports'] for item in checked['checks']] == [741, 3, 336, 741, 741]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms']
    and item['declaration_checks'] == 0 for item in checked['checks'])
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert receipt['source_files'] == 6284 and receipt['direct_audit_imports'] == 5284
assert receipt['audited_theorems'] == commit['audited_theorems'] == selection['prior_publication_audited_theorems']
assert receipt['pins_independently_reverified'] == selection['prior_publication_pins_reverified']
assert receipt['actual_rawFold_source_Seeds_transition_checked'] and receipt['actual_cached_fold_source_Seeds_transition_checked']
assert receipt['actual_terminal_source_Seeds_transition_checked']
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

# Root may commit documentation after Source61. Source and toolchain must stay exact.
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
assert item['module'] == 'SourcePruningEnumerationSharedChildDispatchQueryEvents'
assert selection['compile_order'] == [item['module']]
assert not (ROOT / 'lean/MicroCFTA' / item['source']).exists(), 'This candidate must remain a new normal module.'
packet = BASE / item['packet']
bind_packet(packet, item['manifest_sha256'])
for record in json.loads((packet / 'SOURCE-PINS.json').read_text())['files']:
    verify(ROOT / record['file'], record)
raw = verify(packet / item['source'], {'bytes': item['raw_bytes'], 'sha256': item['raw_sha256']})
for name, digest in item['headers'].items():
    header = verify(packet / name, digest)
    assert raw.count(header.rstrip()) == 1
assert re.findall(r'^theorem (\w+)', raw.decode(), re.M) == ['observe_exact', 'observe_original_source_query_resources_and_seeds']
assert re.findall(r'^noncomputable def (\w+)', raw.decode(), re.M) == ['observe']
assert not re.findall(r'^(?:private theorem |(?:private )?(?:inductive|structure) )', raw.decode(), re.M)
assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', raw)
assert not re.search(rb'\b(?:sorry|axiom)\b', raw)
probe = verify(packet / item['probe'], item['probe_sha256'])
assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['public_qnames']
assert re.findall(r'^#check (\S+)', probe.decode(), re.M) == [item['definition_qname']]
assert probe.count(b'#print axioms ') == item['expected_axiom_reports'] == 2
assert probe.count(b'#check ') == item['expected_declaration_checks'] == 1
assert b'#print axioms ' not in raw and b'#check ' not in raw
for module, digest in item['normal_dependencies'].items():
    verify(ROOT / 'lean/MicroCFTA' / (module + '.lean'), digest)

# Preserve the actual rejected60181 attempt. Printed reports gave no credit.
first_control = BASE / selection['first_controller']
bind_packet(first_control, selection['first_controller_manifest_sha256'])
first_runtime = BASE / selection['first_runtime']
rejected = json.loads((ROOT / selection['first_failure_receipt']).read_text())
first_actual = json.loads((ROOT / selection['first_actual_run_receipt']).read_text())
first_results = json.loads((first_runtime / 'results.json').read_text())
first_pins = json.loads((first_runtime / 'source-pins.json').read_text())
assert rejected['actual_session'] == first_actual['actual_session'] == selection['first_failed_actual_session'] == 60181
assert rejected['actual_terminal'] and first_actual['actual_terminal']
assert rejected['actual_terminal_exit'] == first_actual['actual_terminal_exit'] == 1
assert rejected['runtime'] == first_actual['runtime'] == selection['first_runtime']
assert rejected['checks'] == first_results['checks'] and len(first_results['checks']) == 1
failed = first_results['checks'][0]
assert failed['exit'] == failed['diagnostics'] == failed['declaration_checks'] == 1
assert failed['total_axiom_reports'] == failed['axiom_groups'] == 2
assert failed['sorryAx'] and failed['nonstandard_axioms'] == ['sorryAx']
assert rejected['credited_public_reports'] == first_results['credited_public_reports'] == 0
assert not first_results['proof_credit'] and first_results['source_pins_unchanged']
assert not (first_runtime / 'checked.json').exists()
assert SHA((first_runtime / 'results.json').read_bytes()) == rejected['results_sha256']
assert SHA((first_runtime / 'source-pins.json').read_bytes()) == rejected['source_pins_sha256']
assert len(first_pins) == rejected['pins_independently_reverified'] == 9064
for name, digest in first_pins.items():
    verify(ROOT / name, digest)
first_log = (first_runtime / (item['module'] + '.txt')).read_text()
assert 'Unknown identifier `Interned`' in first_log
assert len(re.findall(r': error(?:\(|:)', first_log)) == 1
comparison = json.loads((packet / 'REPAIR-COMPARISON.json').read_text())
original_packet = BASE / comparison['original_packet']
bind_packet(original_packet, comparison['original_manifest_sha256'])
original_raw = verify(original_packet / item['source'], comparison['original_raw_sha256'])
needle = b'open InternedConstructorTemplates InternedProbeProvenance\n'
assert original_raw.count(needle) == 1
assert raw == original_raw.replace(needle, needle + b'open Cache (Interned)\n', 1)
assert len(raw) - len(original_raw) == 22
for name, digest in comparison['unchanged_payloads'].items():
    assert verify(original_packet / name, digest) == verify(packet / name, digest)
assert original_raw + b'\n' + (original_packet / item['probe']).read_bytes() == (first_runtime / 'source/MicroCFTA' / item['source']).read_bytes()
# The old temporary object directory was cleaned. Its existence is not a gate.

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
assert len(order) == 2546 and len(seen - {item['module']}) == 2545
for name in seen - {item['module']}:
    assert (normal_objects / (name + '.olean')).is_file(), name
assert set(item['normal_dependencies']).issubset(seen)
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((CONTROL / name).read_text())
# Root creates the fresh runtime only after every read-only gate passes.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-child-dispatch-query-seeds-repair-'))
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
    'normal_dependency_modules': 2545, 'cache_data_copied': False}, indent=2) + '\n')
fixture = runtime / 'source/MicroCFTA' / item['source']
fixture.parent.mkdir(parents=True)
fixture.write_bytes(raw + b'\n' + probe)
bound.add(fixture)
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
(runtime / 'NORMAL-STAGING-GATE.json').write_text(json.dumps({
    'source_commit': selection['source_commit'], 'prior_Work61_push_receipt': selection['prior_push_verified_receipt'],
    'checkpoint_commit': push['checkpoint_commit'], 'private_check_requires_checkpoint_push': True,
    'normal_Source_staging_requires_checkpoint_push': True, 'normal_Source_staging_executed_by_this_controller': False}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 1,
    'expected_public_reports': 2, 'explicit_private_reports': 0, 'new_private_helpers': 0, 'definition_checks': 1, 'definition_axiom_credit': 0,
    'new_observer_definitions': 1,
    'normal_Source_changed': False, 'prior_checkpoint_push_required_before_private_check': True}))
