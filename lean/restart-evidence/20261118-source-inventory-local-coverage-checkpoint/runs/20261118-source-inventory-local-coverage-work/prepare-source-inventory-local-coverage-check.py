from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-source-inventory-local-coverage-check-control-draft'
WORK = BASE / '20261118-source-inventory-local-coverage-work'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-source-inventory-local-coverage-check.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


# These two statuses deliberately prevent execution of this OPEN draft.
manifest = json.loads((CONTROL / 'MANIFEST.json').read_text())
assert manifest['status'] == 'FROZEN PRIVATE CHECK CONTROLLER / NOT EXECUTED'
for name, record in manifest['files'].items():
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
s = json.loads((CONTROL / 'SELECTION.json').read_text())
assert s['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert s['work'] == WORK.name and s['entrypoint'] == Path(__file__).name
assert s['runtime'] == '20261118-source-inventory-local-coverage-check'
assert s['expected_checks'] == 3 and s['expected_axiom_reports'] == 4
assert s['expected_private_reports'] == s['expected_public_reports'] == 2
assert s['new_private_theorems'] == s['new_public_theorems'] == 2
assert s['new_definitions'] == s['new_helpers'] == s['new_constructors'] == s['expected_definition_checks'] == 0
assert not s['full_coverage_producer334c_proved']
runtime = BASE / s['runtime']
assert not runtime.exists(), 'Use a new runtime. Preserve historical attempts.'
receipt_pins = json.loads((CONTROL / 'RECEIPT-PINS.json').read_text())
for name, record in receipt_pins.items():
    verify(ROOT / name, record)
prior = BASE / s['prior_work']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
publication = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
push = json.loads((prior / 'PUSH-VERIFIED.json').read_text())
assert commit['source_commit'] == push['source_commit'] == s['source_commit']
assert commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert publication['actual_terminal'] and actual['actual_terminal']
assert publication['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert publication['actual_session'] == actual['actual_session'] == commit['publication_actual_session'] == s['publication_actual_session']
assert publication['runtime'] == s['publication_runtime']
assert publication['all_five_gates_passed'] and publication['proof_credit']
assert publication['source_files'] == s['source_files'] == 6288
assert publication['direct_audit_imports'] == 5288
assert publication['audited_theorems'] == s['prior_publication_audited_theorems'] == commit['audited_theorems']
assert [item['total_axiom_reports'] for item in publication['checks']] == s['prior_publication_gate_reports']
assert [item['declaration_checks'] for item in publication['checks']] == s['prior_publication_definition_checks']
assert push['checkpoint_commit'] == push['remote_commit'] == s['checkpoint_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
assert push['archive_manifest_sha256'] == s['archive_manifest_sha256']
assert push['source_tree_sha256'] == s['source_tree_sha256']
verify(ROOT / s['archive_manifest'], s['archive_manifest_sha256'])
assert not publication['joint_finite_completion_proved']
pubrun = BASE / s['publication_runtime']
checked_data = verify(pubrun / 'checked.json', publication['checked_sha256'])
assert SHA(verify(pubrun / 'results.json', publication['results_sha256'])) == SHA(checked_data)
checked = json.loads(checked_data)
assert checked['checks'] == publication['checks'] and checked['all_five_gates_passed']
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in checked['checks'])
pubpins = json.loads(verify(pubrun / 'source-pins.json', publication['source_pins_sha256']))
assert len(pubpins) == publication['pins_independently_reverified'] == s['publication_pins'] == 11192
for name, record in pubpins.items():
    verify(ROOT / name, record)

# Current compilation uses published Source69. Historical snapshots never replace compiler inputs.
subprocess.run(['git', 'merge-base', '--is-ancestor', s['source_commit'], 'HEAD'], cwd=ROOT, check=True)
subprocess.run(['git', 'diff', '--quiet', s['source_commit'], '--', 'lean/MicroCFTA',
    'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / s['source_baseline']).read_text())
normalpins = json.loads((prior / 'NORMAL-SOURCE-PINS.json').read_text())
assert baseline['source_commit'] == s['source_commit']
assert len(normalpins) == s['source_toolchain_pins'] == 6292
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == s['source_files'] == 6288
assert set(baseline['sources']) == {str(path.relative_to(ROOT)) for path in sources}
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert normalpins[name] == record['sha256']
overrides = json.loads((CONTROL / s['historical_overrides']).read_text())
stage = json.loads((ROOT / s['historical_overrides_stage']).read_text())
assert overrides == stage['baseline_overrides']


def verify_historical(name, record):
    path = ROOT / name
    digest = record['sha256'] if isinstance(record, dict) else record
    if path.is_file() and SHA(path.read_bytes()) == digest:
        return verify(path, record)
    assert name in overrides, 'No authorized Source69 BEFORE snapshot: ' + name
    return verify(ROOT / overrides[name], record)


packet = BASE / s['candidate']
candidate = json.loads(verify(packet / 'MANIFEST.json', s['candidate_manifest_sha256']))
for name, record in candidate['files'].items():
    verify(packet / name, record)
assert json.loads((packet / 'NORMAL-SOURCE-PINS.json').read_text()) == normalpins
inputs = json.loads((packet / 'SOURCE-PINS.json').read_text())['files']
assert len(inputs) == 2904
for name, record in inputs.items():
    verify_historical(name, record)
dependencies = json.loads((packet / 'DEPENDENCY-PINS.json').read_text())['immutable_dependencies']
assert len(dependencies) == 15
for record in dependencies:
    verify(ROOT / record['path'], record)
review_path = ROOT / s['candidate_Root_review_receipt']
assert str(review_path.relative_to(ROOT)) in receipt_pins
review = json.loads(review_path.read_text())
assert review['manifest_sha256'] == s['candidate_manifest_sha256']
assert review['all_three_sources_and_four_FIRSTs_and_proofs_pass_through_unchanged']
assert review['whole_Source69_Shared_prefix_exact_at_zero']
assert review['reports_per_owning_module'] == [2, 1, 1]
assert not review['full_producer334c_proved'] and not review['compiled'] and not review['proof_credit']
selected = json.loads((packet / 'COMPONENTS.json').read_text())
assert selected['compile_order'] == s['compile_order']
assert selected['reports_per_owner'] == [2, 1, 1] and not selected['full_coverage_producer334c_selected']
raws = {}
fixtures = {}
for item, original in zip(s['components'], selected['components'], strict=True):
    for key in original:
        assert item[key] == original[key], (item['module'], key)
    name = item['module']
    assert re.fullmatch(r'[A-Za-z0-9_]+', name)
    assert item['runtime_source'] == 'source/MicroCFTA/' + name + '.lean'
    raw = verify(packet / item['source'], item['raw'])
    assert raw == verify(ROOT / item['origin_source']['path'], item['origin_source'])
    if item['new_module']:
        assert not (ROOT / 'lean/MicroCFTA' / (name + '.lean')).exists(), 'New module collision.'
        added = raw
    else:
        old = verify(ROOT / 'lean/MicroCFTA' / (name + '.lean'), item['old_owner'])
        added = verify(packet / item['append'], json.loads((packet / 'ASSEMBLY.json').read_text())['Shared_append'])
        assert item['old_owner_offset'] == 0 and raw == old + added
    assert not re.search(rb'\b(?:sorry|axiom)\b', added)
    assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', added)
    for pair in item['headers_and_proofs']:
        header = verify(packet / pair['header']['file'], pair['header'])
        body = verify(packet / pair['proof']['file'], pair['proof'])
        if pair['join_mode'] == 'header_plus_proof':
            complete = header + body
        elif pair['join_mode'] == 'remove_final_header_LF_then_original_same_line_delimiter':
            assert header.endswith(b'\n')
            complete = header[:-1] + b' := by\n' + body
        else:
            assert pair['join_mode'] == 'header_plus_original_next_line_delimiter'
            complete = header + b' := by\n' + body
        assert raw.count(complete) == 1
    fixture = verify(packet / item['fixture']['file'], item['fixture'])
    assert fixture == verify(CONTROL / item['fixture']['file'], item['fixture'])
    resolved = []
    namespaces = []
    for line in fixture.decode().splitlines():
        if line.startswith('namespace '):
            namespaces.append(line.removeprefix('namespace '))
        elif line.startswith('end '):
            assert namespaces and namespaces.pop() == line.removeprefix('end ')
        elif line.startswith('#print axioms '):
            query = line.removeprefix('#print axioms ')
            resolved.append(query if query.startswith('MicroCFTA.') else '.'.join(namespaces + [query]))
        else:
            assert not line.strip(), 'Unexpected fixture command.'
    assert not namespaces and resolved == item['private_qnames'] + item['public_qnames']
    assert item['definition_qnames'] == [] and item['expected_declaration_checks'] == 0
    raws[name] = raw
    fixtures[name] = fixture
assert len(raws) == 3 and set(raws) == set(s['compile_order'])
paths = {path.stem: path for path in sources}
seen, active, order, graph = set(), [], [], {}


def visit(name):
    assert name not in active, 'Import cycle: ' + repr(active + [name])
    if name in seen:
        return
    active.append(name)
    text = raws[name].decode() if name in raws else paths[name].read_text()
    graph[name] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', text, re.M)
    for dependency in graph[name]:
        visit(dependency)
    active.pop()
    seen.add(name)
    order.append(name)


for name in s['compile_order']:
    visit(name)
topo = json.loads((CONTROL / 'TOPOLOGICAL-ORDER.json').read_text())
assert graph == topo['direct_imports'] and order == topo['full_transitive_order']
assert len(order) == s['expected_total_modules'] == 2877
assert len(seen - set(raws)) == s['expected_normal_dependencies'] == 2874
assert [name for name in order if name in raws] == s['compile_order']
normalobjects = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
for name in seen - set(raws):
    assert (normalobjects / (name + '.olean')).is_file(), name
for filename in ['check-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((CONTROL / filename).read_text())

# Root starts mutation only after all read-only gates pass.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-source-inventory-local-coverage-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for obj in sorted(normalobjects.glob('*.olean')):
    if obj.stem not in raws:
        (objects / 'MicroCFTA' / obj.name).symlink_to(obj)
        linked.append(obj.name)
assert all(name + '.olean' not in linked for name in raws)
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'excluded_candidate_modules': list(raws),
    'linked_unchanged_modules': linked, 'cache_data_copied': False}, indent=2) + '\n')
for item in s['components']:
    fixture = runtime / item['runtime_source']
    assert fixture == runtime / 'source/MicroCFTA' / (item['module'] + '.lean')
    fixture.parent.mkdir(parents=True, exist_ok=True)
    fixture.write_bytes(raws[item['module']] + b'\n' + fixtures[item['module']])
    bound.add(fixture)
(runtime / 'selection.json').write_text(json.dumps(s, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'commands': 3,
    'public_axiom_reports': 2, 'private_axiom_reports': 2, 'definition_checks': 0,
    'definition_axiom_credit': 0, 'normal_Source_changed': False}))
