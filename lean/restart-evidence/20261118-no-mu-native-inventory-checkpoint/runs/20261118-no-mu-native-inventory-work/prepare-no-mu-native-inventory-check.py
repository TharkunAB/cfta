from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-no-mu-native-inventory-check-control-draft'
WORK = BASE / '20261118-no-mu-native-inventory-work'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-no-mu-native-inventory-check.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


# Root must freeze this OPEN packet before executing a copied preparer.
manifest = json.loads((CONTROL / 'MANIFEST.json').read_text())
assert manifest['status'] == 'FROZEN PRIVATE CHECK CONTROLLER / NOT EXECUTED'
for name, record in manifest['files'].items():
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
s = json.loads((CONTROL / 'SELECTION.json').read_text())
assert s['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert s['work'] == WORK.name and s['entrypoint'] == Path(__file__).name
assert s['runtime'] == '20261118-no-mu-native-inventory-check'
assert s['expected_checks'] == s['expected_axiom_reports'] == s['expected_public_reports'] == 1
assert s['expected_private_reports'] == s['expected_definition_checks'] == 0
assert s['new_public_theorems'] == 1
assert s['new_private_theorems'] == s['new_definitions'] == s['new_helpers'] == s['new_constructors'] == 0
assert s['checkpoint_commit'] is None and s['checkpoint_push_receipt'] is None
assert not s['checkpoint_push_required_for_private_check']
runtime = BASE / s['runtime']
assert not runtime.exists(), 'Use a new runtime. Preserve historical attempts.'
for name, record in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
prior = BASE / s['prior_work']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
commit_actual = json.loads((prior / 'SOURCE-COMMIT-ACTUAL-RUN.json').read_text())
publication = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
assert commit['source_commit'] == commit_actual['source_commit'] == s['source_commit']
assert commit['actual_terminal'] and commit_actual['actual_terminal']
assert commit['actual_terminal_exit'] == commit_actual['actual_terminal_exit'] == 0
assert publication['actual_terminal'] and actual['actual_terminal']
assert publication['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert publication['actual_session'] == actual['actual_session'] == commit['publication_actual_session'] == s['publication_actual_session']
assert publication['runtime'] == actual['runtime'] == s['publication_runtime']
assert publication['all_five_gates_passed'] and actual['all_five_gates_passed'] and publication['proof_credit']
assert publication['source_files'] == commit['source_files'] == s['source_files'] == 6290
assert publication['direct_audit_imports'] == commit['audit_imports'] == 5290
assert publication['audited_theorems'] == s['prior_publication_audited_theorems'] == commit['audited_theorems'] == 100312
assert [item['total_axiom_reports'] for item in publication['checks']] == s['prior_publication_gate_reports'] == [751, 4, 346, 751, 751]
assert [item['declaration_checks'] for item in publication['checks']] == s['prior_publication_definition_checks'] == [0, 0, 0, 0, 0]
assert not publication['joint_finite_completion_proved']
pubrun = BASE / s['publication_runtime']
checked_data = verify(pubrun / 'checked.json', publication['checked_sha256'])
assert SHA(verify(pubrun / 'results.json', publication['results_sha256'])) == SHA(checked_data)
checked = json.loads(checked_data)
assert checked['checks'] == publication['checks'] and checked['all_five_gates_passed']
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in checked['checks'])
pubpins = json.loads(verify(pubrun / 'source-pins.json', publication['source_pins_sha256']))
assert len(pubpins) == publication['pins_independently_reverified'] == s['publication_pins'] == 11467
for name, record in pubpins.items():
    verify(ROOT / name, record)

# A later documentation commit may advance HEAD without changing the Source baseline.
subprocess.run(['git', 'merge-base', '--is-ancestor', s['source_commit'], 'HEAD'], cwd=ROOT, check=True)
subprocess.run(['git', 'diff', '--quiet', s['source_commit'], '--', 'lean/MicroCFTA',
    'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / s['source_baseline']).read_text())
normalpins = json.loads((prior / 'NORMAL-SOURCE-PINS.json').read_text())
assert baseline['source_commit'] == s['source_commit']
assert len(normalpins) == s['source_toolchain_pins'] == 6294
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == s['source_files'] == 6290
assert set(baseline['sources']) == {str(path.relative_to(ROOT)) for path in sources}
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert normalpins[name] == record['sha256']
overrides = json.loads((CONTROL / s['historical_overrides']).read_text())
assert overrides == json.loads((ROOT / s['historical_overrides_stage']).read_text())['baseline_overrides']


def verify_historical(name, record):
    path = ROOT / name
    digest = record['sha256'] if isinstance(record, dict) else record
    if path.is_file() and SHA(path.read_bytes()) == digest:
        return verify(path, record)
    assert name in overrides, 'No authorized Source70 BEFORE snapshot: ' + name
    return verify(ROOT / overrides[name], record)


# The old engine is evidence for this adaptation. It does not supply checked reports.
oldcontrol = BASE / s['base_control']
oldmanifest = json.loads(verify(oldcontrol / 'MANIFEST.json', s['base_control_manifest_sha256']))
for name, record in oldmanifest['files'].items():
    verify(oldcontrol / name, record)
packet = BASE / s['candidate']
candidate = json.loads(verify(packet / 'MANIFEST.json', s['candidate_manifest_sha256']))
assert candidate['status'] == 'FROZEN UNCOMPILED CANDIDATE; zero theorem credit'
for name, record in candidate['files'].items():
    verify(packet / name, record)
for name, record in json.loads((packet / 'SOURCE-PINS.json').read_text())['files'].items():
    verify(ROOT / name, record)
dependencies = json.loads((packet / 'DEPENDENCY-PINS.json').read_text())['files']
for name, record in dependencies.items():
    verify(ROOT / name, record)
    if name.endswith('/MANIFEST.json'):
        audit_root = (ROOT / name).parent
        audit_manifest = json.loads((ROOT / name).read_text())
        for local, expected in audit_manifest['files'].items():
            verify(audit_root / local, expected)
        audit_pins = json.loads((audit_root / 'SOURCE-PINS.json').read_text())['files']
        for historical, expected in audit_pins.items():
            verify_historical(historical, expected)
selected = json.loads((packet / 'COMPONENTS.json').read_text())
assert len(selected['components']) == 1 and selected['commands'] == 1
item = s['components'][0]
original = selected['components'][0]
name = item['module']
assert re.fullmatch(r'[A-Za-z0-9_]+', name)
assert original['module'] == 'MicroCFTA.' + name
assert original['source_file'] == item['source'] == name + '.lean'
assert item['runtime_source'] == 'source/MicroCFTA/' + name + '.lean'
assert not (ROOT / 'lean/MicroCFTA' / (name + '.lean')).exists(), 'New module collision.'
assert item['raw']['sha256'] == original['raw_sha256'] and item['raw']['bytes'] == original['raw_bytes']
raw = verify(packet / item['source'], item['raw'])
first = verify(packet / item['first_file'], item['first'])
proof = verify(packet / item['proof_file'], item['proof'])
assert original['first_file'] == item['first_file'] and original['first_sha256'] == item['first']['sha256']
assert original['proof_file'] == item['proof_file']
assert first == (BASE / '20261118-no-mu-source-native-request-inventory-audit-line-correction/FIRST-HEADER.lean.txt').read_bytes()
assert item['first']['sha256'] == '4d2f1c85583b173093b81d41b8942da6861d7761d3a26b940fde79252adc6499'
assert raw == (packet / 'PREAMBLE.lean.txt').read_bytes() + first + b' := ' + proof + b'\nend MicroCFTA.SourceCurrentNativeNoMuInventory\n'
assert not re.search(rb'\b(?:sorry|axiom)\b', raw)
assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', raw)
assert len(re.findall(rb'^theorem ', raw, re.M)) == 1
assert not re.search(rb'^(?:private )?(?:theorem|def|structure|inductive|opaque) ', proof, re.M)
fixture = verify(CONTROL / item['fixture']['file'], item['fixture'])
assert fixture == verify(packet / item['candidate_fixture'], item['fixture'])
assert fixture.decode().splitlines() == ['#print axioms ' + item['public_qnames'][0]]
assert original['public_names'] == item['public_qnames']
assert item['private_qnames'] == original['private_names'] == []
assert item['definition_qnames'] == original['definition_names'] == []
assert s['compile_order'] == [name]
paths = {path.stem: path for path in sources}
seen, active, order, graph = set(), [], [], {}


def visit(module):
    assert module not in active, 'Import cycle: ' + repr(active + [module])
    if module in seen:
        return
    active.append(module)
    content = raw.decode() if module == name else paths[module].read_text()
    graph[module] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', content, re.M)
    for dependency in graph[module]:
        visit(dependency)
    active.pop()
    seen.add(module)
    order.append(module)


visit(name)
topo = json.loads((CONTROL / 'TOPOLOGICAL-ORDER.json').read_text())
assert graph == topo['direct_imports'] and order == topo['full_transitive_order']
assert len(order) == s['expected_total_modules'] == 1626
assert len(seen - {name}) == s['expected_normal_dependencies'] == 1625
assert order[-1] == name and topo['selected_compile_order'] == [name]
normalobjects = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
for dependency in seen - {name}:
    assert (normalobjects / (dependency + '.olean')).is_file(), dependency
for filename in ['check-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((CONTROL / filename).read_text())

# Root starts mutation only after all read-only gates pass.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-no-mu-native-inventory-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for obj in sorted(normalobjects.glob('*.olean')):
    if obj.stem != name:
        (objects / 'MicroCFTA' / obj.name).symlink_to(obj)
        linked.append(obj.name)
assert name + '.olean' not in linked
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'excluded_candidate_modules': [name],
    'linked_unchanged_modules': linked, 'cache_data_copied': False}, indent=2) + '\n')
fixture_path = runtime / item['runtime_source']
assert fixture_path == runtime / 'source/MicroCFTA' / (name + '.lean')
fixture_path.parent.mkdir(parents=True, exist_ok=True)
fixture_path.write_bytes(raw + b'\n' + fixture)
bound.add(fixture_path)
(runtime / 'selection.json').write_text(json.dumps(s, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'commands': 1,
    'public_axiom_reports': 1, 'private_axiom_reports': 0, 'definition_checks': 0,
    'definition_axiom_credit': 0, 'normal_Source_changed': False}))
