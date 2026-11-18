from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-worker-endpoint-seeds-step-check-control-draft'
WORK = BASE / '20261118-worker-endpoint-seeds-step-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root copies the reviewed preparer into its Work directory.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-worker-endpoint-seeds-step-check.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


def bind_packet(packet, digest):
    manifest = json.loads(verify(packet / 'MANIFEST.json', digest))
    for name, record in manifest['files'].items():
        verify(packet / name, record)
    return manifest


manifest = json.loads((CONTROL / 'MANIFEST.json').read_text())
assert manifest['status'] == 'FROZEN PRIVATE CHECK CONTROLLER / NOT EXECUTED'
for name, record in manifest['files'].items():
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
selection = json.loads((CONTROL / 'SELECTION.json').read_text())
assert selection['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert selection['work'] == WORK.name
assert selection['runtime'] == '20261118-worker-endpoint-seeds-step-check'
assert re.fullmatch(r'[0-9a-f]{40}', selection['source_commit'])
assert re.fullmatch(r'[0-9a-f]{40}', selection['verified_prior_checkpoint_commit'])
assert selection['expected_checks'] == len(selection['components']) == 3
assert selection['expected_public_axiom_reports'] == 2
assert selection['expected_explicit_private_axiom_reports'] == 3
assert selection['expected_total_axiom_reports'] == 5
assert selection['expected_declaration_checks'] == selection['new_definitions'] == 0
assert selection['new_public_theorems'] == 2 and selection['new_private_theorems'] == 6
assert selection['new_private_helpers_transitive'] == 3
assert selection['rebuilt_Source65_leaf_and_zero_base_extra_credit'] == 0
assert selection['prior_checkpoint_push_required_for_private_check']
assert selection['prior_checkpoint_push_required_before_normal_Source_staging']
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Preserve every prior runtime. Use a fresh namespace.'
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
assert [item['total_axiom_reports'] for item in checked['checks']] == [744, 2, 339, 744, 744]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in checked['checks'])
assert checked['checks'][1]['declaration_checks'] == 3
assert [item['declaration_checks'] for item in checked['checks']] == selection['prior_publication_declaration_checks']
# Historical independent declaration checks remain bound exactly by checked.json.
# They do not add fresh axiom credit in this next private check.
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert receipt['source_files'] == 6286 and receipt['direct_audit_imports'] == 5286
assert receipt['audited_theorems'] == commit['audited_theorems'] == selection['prior_publication_audited_theorems']
assert receipt['pins_independently_reverified'] == selection['prior_publication_pins_reverified']
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

# Root may commit documentation later. Source and toolchain must stay exact.
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
for parent in json.loads((CONTROL / 'DEPENDENT-PACKETS.json').read_text()):
    bind_packet(BASE / parent['packet'], parent['manifest_sha256'])
raw_by_module = {}
probes_by_module = {}
for item in selection['components']:
    packet = BASE / item['packet']
    bind_packet(packet, item['manifest_sha256'])
    source_pins = json.loads((packet / 'SOURCE-PINS.json').read_text())['files']
    for name, record in source_pins.items():
        verify(ROOT / name, record)
    raw = verify(packet / item['source'], {'bytes': item['raw_bytes'], 'sha256': item['raw_sha256']})
    old = verify(ROOT / item['old_owner_source'], {'bytes': item['old_owner_bytes'], 'sha256': item['old_owner_sha256']})
    assert raw.startswith(old), item['module']
    if 'append' in item:
        assert raw == old + verify(packet / item['append'], item['append_sha256'])
    else:
        for layer in item['exact_prefix_chain']:
            parent = BASE / layer['packet']
            assembly = json.loads((parent / 'ASSEMBLY.json').read_text())
            prefix = (BASE / assembly['prefix_packet'] / item['source']).read_bytes()
            assert (parent / item['source']).read_bytes() == prefix + (parent / 'APPEND.lean.txt').read_bytes()
        assert item['module'] == 'SourcePruningEnumerationSharedEagerReservation'
    for header in item['headers']:
        data = verify(BASE / header['packet'] / header['file'], header['sha256'])
        assert raw.count(data.rstrip()) == 1
    added = raw[len(old):]
    assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', added)
    assert not re.search(rb'\b(?:sorry|axiom)\b', added)
    assert not re.search(r'^(?:private )?(?:noncomputable )?(?:def|inductive|structure) ', added.decode(), re.M)
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    probe_root = packet if item['probe_origin'] == 'candidate' else CONTROL
    probe = verify(probe_root / item['probe'], item['probe_sha256'])
    qnames = item['public_qnames'] if item['report_kind'] == 'public' else item['private_qnames']
    assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == qnames
    assert probe.count(b'#print axioms ') == item['expected_axiom_reports']
    assert b'#check ' not in probe and item['expected_declaration_checks'] == 0
    raw_by_module[item['module']] = raw
    probes_by_module[item['module']] = probe
assert sum(item['expected_axiom_reports'] for item in selection['components'] if item['report_kind'] == 'public') == 2
assert sum(item['expected_axiom_reports'] for item in selection['components'] if item['report_kind'] == 'private') == 3
normal_objects = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
paths = {path.stem: path for path in sources}
active, seen, order, graph = [], set(), [], {}


def visit(name):
    assert name not in active, 'Import cycle: ' + repr(active + [name])
    if name in seen:
        return
    active.append(name)
    data = raw_by_module[name].decode() if name in raw_by_module else paths[name].read_text()
    graph[name] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', data, re.M)
    for dependency in graph[name]:
        assert dependency in paths, dependency
        visit(dependency)
    active.pop()
    seen.add(name)
    order.append(name)


for item in selection['components']:
    visit(item['module'])
topological = json.loads((CONTROL / 'TOPOLOGICAL-ORDER.json').read_text())
assert graph == topological['direct_imports'] and order == topological['full_transitive_order']
assert len(order) == 2866 and len(seen - set(raw_by_module)) == 2863
assert [name for name in order if name in raw_by_module] == selection['compile_order']
for name in seen - set(raw_by_module):
    assert (normal_objects / (name + '.olean')).is_file(), name
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((CONTROL / name).read_text())
# Root starts mutation only after all read-only gates pass.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-worker-endpoint-seeds-step-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for obj in sorted(normal_objects.glob('*.olean')):
    if obj.stem not in raw_by_module:
        (objects / 'MicroCFTA' / obj.name).symlink_to(obj)
        linked.append(obj.name)
assert all(name + '.olean' not in linked for name in raw_by_module)
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'linked_unchanged_modules': linked,
    'excluded_candidate_modules': list(raw_by_module), 'candidate_output_links_created': False,
    'normal_dependency_modules': 2863, 'cache_data_copied': False}, indent=2) + '\n')
for item in selection['components']:
    fixture = runtime / 'source/MicroCFTA' / item['source']
    fixture.parent.mkdir(parents=True, exist_ok=True)
    fixture.write_bytes(raw_by_module[item['module']] + b'\n' + probes_by_module[item['module']])
    bound.add(fixture)
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
(runtime / 'NORMAL-STAGING-GATE.json').write_text(json.dumps({'source_commit': selection['source_commit'],
    'prior_Source65_push_receipt': selection['prior_push_verified_receipt'], 'checkpoint_commit': push['checkpoint_commit'],
    'private_check_requires_checkpoint_push': True, 'normal_Source_staging_requires_checkpoint_push': True,
    'normal_Source_staging_executed_by_this_controller': False}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 3,
    'expected_public_reports': 2, 'expected_private_reports': 3, 'growth_helpers_transitive': 3,
    'rebuilt_prior_leaf_and_zero_base_extra_credit': 0, 'definition_checks': 0, 'new_definitions': 0,
    'normal_Source_changed': False}))
