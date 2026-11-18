from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-terminal-query-resources-work59-label-repair-control-draft'
WORK = BASE / '20261118-terminal-query-resources-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root reviews and copies this preparer into the new Work directory.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-private-check.py').read_bytes()
selection = json.loads((CONTROL / 'SELECTION.json').read_text())
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Use a new runtime and preserve every prior attempt.'
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


for name, record in records(json.loads((CONTROL / 'MANIFEST.json').read_text())):
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
for name, record in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
assert selection['source_commit'] == '04e2eb843816747cab7ec59a150d0897619274b4'
assert selection['source_files'] == 6283
assert selection['expected_checks'] == len(selection['components']) == 1
assert selection['expected_public_axiom_reports'] == 1
assert selection['expected_explicit_private_axiom_reports'] == selection['expected_declaration_checks'] == 0
assert selection['new_private_helpers_transitive'] == 1 and selection['new_definitions'] == 0
assert not selection['prior_checkpoint_push_required_for_private_check']
assert selection['prior_checkpoint_push_required_before_normal_Source_staging']
assert selection['prior_checkpoint_commit_is_dynamic']
prior = BASE / selection['prior_work']
publication = BASE / selection['prior_publication_runtime']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
receipt = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
checked = json.loads((publication / 'checked.json').read_text())
assert commit['source_commit'] == selection['source_commit'] and commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert commit['publication_actual_session'] == receipt['actual_session'] == actual['actual_session'] == 72663
assert receipt['actual_terminal'] and actual['actual_terminal']
assert receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert checked == json.loads((publication / 'results.json').read_text()) and checked['checks'] == receipt['checks']
assert SHA((publication / 'checked.json').read_bytes()) == receipt['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == receipt['source_pins_sha256']
assert [item['total_axiom_reports'] for item in checked['checks']] == [735, 2, 330, 735, 735]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms']
    and item['declaration_checks'] == 0 for item in checked['checks'])
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert receipt['source_files'] == 6283 and receipt['direct_audit_imports'] == 5283
assert receipt['audited_theorems'] == commit['audited_theorems'] == 100218
assert receipt['pins_independently_reverified'] == 8398
assert not receipt['joint_finite_completion_proved']
assert len(json.loads((publication / 'source-pins.json').read_text())) == 8398
for name, digest in json.loads((publication / 'source-pins.json').read_text()).items():
    verify(ROOT / name, digest)
commit_actual = json.loads((prior / 'SOURCE-COMMIT-ACTUAL-RUN.json').read_text())
assert commit_actual['actual_session'] == 22154 and commit_actual['actual_terminal'] and commit_actual['actual_terminal_exit'] == 0
assert commit_actual['source_commit'] == commit['source_commit'] == selection['source_commit']
assert commit_actual['parent'] == commit['parent'] == '6546febba4473d4347d8e4d4c68ea1c90cb7dae3'
assert commit_actual['source_payload_files'] == len(commit['files']) == 2
assert set(commit['files']) == {'lean/MicroCFTA/SourcePruningEnumerationSharedTerminalFoldQueryEvents.lean', 'lean/MicroCFTA/Audit.lean'}
# Documentation and frozen evidence may advance HEAD after this Source commit.
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', selection['source_commit'], 'HEAD'], cwd=ROOT, check=True)
changes = subprocess.check_output(['git', 'diff', '--name-only', selection['source_commit'], 'HEAD'], cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md'] or name.startswith('lean/restart-evidence/') for name in changes), changes
subprocess.run(['git', 'diff', '--quiet', selection['source_commit'], 'HEAD', '--',
    'lean/MicroCFTA', 'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / selection['source_baseline']).read_text())
assert baseline['source_commit'] == selection['source_commit'] and baseline['source_files'] == 6283
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert {str(path.relative_to(ROOT)) for path in sources} == set(baseline['sources']) and len(sources) == 6283
public_pins = json.loads((publication / 'source-pins.json').read_text())
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert public_pins[name] == record['sha256'], name
item = selection['components'][0]
assert selection['compile_order'] == [item['module']]
packet = BASE / item['packet']
manifest = json.loads(verify(packet / 'MANIFEST.json', item['manifest_sha256']))
for name, record in records(manifest):
    verify(packet / name, record)
source_pins = json.loads((packet / 'SOURCE-PINS.json').read_text())
history = selection['candidate_historical_SOURCE_PINS_overrides_only']
assert history == json.loads((CONTROL / 'HISTORICAL-PIN-OVERRIDE.json').read_text())['overrides']
assert set(history) == {'lean/MicroCFTA/SourcePruningEnumerationSharedTerminalFoldQueryEvents.lean'}
for record in source_pins['files']:
    verify(ROOT / history.get(record['file'], record['file']), record)
# The normal Fold pin and compiler object are current, never the historical owner.
fold = selection['actual_normal_dependency']
assert fold['module'] != selection['compile_order'][0]
verify(ROOT / fold['source_path'], {'sha256': fold['raw_sha256'], 'bytes': fold['raw_bytes']})
assert fold['raw_sha256'] == baseline['sources'][fold['source_path']]['sha256'] == public_pins[fold['source_path']]

raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
before = verify(ROOT / item['owner_source'], {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
assert before == verify(CONTROL / 'OWNER-BEFORE.lean.txt', item['owner_sha256'])
imports = verify(packet / item['imports'], item['imports_sha256'])
appended = verify(packet / item['append'], item['append_sha256'])
assembly = json.loads(verify(packet / item['assembly'], item['assembly_sha256']))
assert len(before) == assembly['normal_owner_bytes'] == 19079
assert len(imports) == item['owner_offset'] == assembly['normal_owner_offset'] == 208
assert raw == imports + before + appended
header = verify(packet / item['header'], item['header_sha256'])
assert header == (CONTROL / 'FIRST-HEADER.lean.txt').read_bytes()
start = appended.index(header.splitlines()[0])
assert appended[start:appended.index(b':= by', start)].rstrip() == header.rstrip()
private_header = verify(packet / item['private_header'], item['private_header_sha256'])
assert private_header == (CONTROL / 'PRIVATE-HEADER.lean.txt').read_bytes()
private_start = appended.index(private_header.splitlines()[0])
assert appended[private_start:appended.index(b':= by', private_start)].rstrip() == private_header.rstrip()
assert len(re.findall(rb'^import ', imports, re.M)) == 3
probe = verify(packet / item['probe'], item['probe_sha256'])
assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['public_qnames']
assert probe.count(b'#print axioms ') == 1 and b'#check ' not in probe
assert b'#print axioms ' not in raw and b'#check ' not in raw
assert re.findall(r'^theorem (\w+)', appended.decode(), re.M) == [item['public_qnames'][0].rsplit('.', 1)[1]]
assert len(re.findall(r'^private theorem ', appended.decode(), re.M)) == item['new_private_helpers_transitive'] == 1
assert not re.findall(r'^(?:private )?(?:def|inductive|structure) ', appended.decode(), re.M)
assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', appended)
assert not re.search(rb'\b(?:sorry|axiom)\b', raw)
# The selected complete module replaces only its own private output object.
normal_objects = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
paths = {path.stem: path for path in sources}
active = []
seen = set()
order = []
graph = {}


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
assert len(order) == 2141 and len(seen - {item['module']}) == 2140
for name in seen - {item['module']}:
    assert (normal_objects / (name + '.olean')).is_file(), name
assert fold['module'] in seen and fold['module'] != item['module']
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((CONTROL / name).read_text())
# Root materializes a fresh runtime only after every read-only gate passes.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-terminal-query-resources-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for obj in sorted(normal_objects.glob('*.olean')):
    if obj.stem != item['module']:
        (objects / 'MicroCFTA' / obj.name).symlink_to(obj)
        linked.append(obj.name)
assert item['module'] + '.olean' not in linked
assert fold['module'] + '.olean' in linked
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'linked_unchanged_modules': linked,
    'excluded_candidate_modules': [item['module']], 'candidate_output_links_created': False,
    'normal_dependency_modules': 2140, 'cache_data_copied': False}, indent=2) + '\n')
fixture = runtime / 'source/MicroCFTA' / item['source']
fixture.parent.mkdir(parents=True)
fixture.write_bytes(raw + b'\n' + probe)
bound.add(fixture)
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
(runtime / 'NORMAL-STAGING-GATE.json').write_text(json.dumps({
    'source_commit': selection['source_commit'], 'required_Work59_push_receipt': selection['prior_push_verified_receipt'],
    'checkpoint_commit': 'READ DYNAMICALLY FROM FINAL Work59/PUSH-VERIFIED.json',
    'private_check_can_precede_checkpoint_push': True, 'normal_Source_staging_requires_checkpoint_push': True,
    'normal_Source_staging_executed_by_this_controller': False}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 1,
    'expected_public_reports': 1, 'explicit_private_reports': 0, 'new_private_helpers': 1,
    'definition_checks': 0, 'old_owner_bytes': 19079, 'old_owner_offset': 208,
    'normal_Source_changed': False, 'prior_checkpoint_push_required_before_normal_Source_staging': True}))
