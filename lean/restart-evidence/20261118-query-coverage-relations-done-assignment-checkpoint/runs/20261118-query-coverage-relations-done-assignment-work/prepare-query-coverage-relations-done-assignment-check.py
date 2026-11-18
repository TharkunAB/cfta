from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-query-coverage-relations-done-assignment-check-control-draft'
WORK = BASE / '20261118-query-coverage-relations-done-assignment-work'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-query-coverage-relations-done-assignment-check.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


manifest = json.loads((CONTROL / 'MANIFEST.json').read_text())
assert manifest['status'] == 'FROZEN PRIVATE CHECK CONTROLLER / NOT EXECUTED'
for name, record in manifest['files'].items():
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
s = json.loads((CONTROL / 'SELECTION.json').read_text())
assert s['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert s['work'] == WORK.name
assert s['runtime'] == '20261118-query-coverage-relations-done-assignment-check'
assert re.fullmatch(r'[0-9a-f]{40}', s['source_commit'])
assert re.fullmatch(r'[0-9a-f]{40}', s['checkpoint_commit'])
assert s['expected_checks'] == 2
assert s['expected_public_reports'] == s['expected_axiom_reports'] == 1
assert s['expected_private_reports'] == s['new_private_theorems'] == s['new_helpers'] == 0
assert s['new_private_Prop_inductives'] == s['expected_definition_checks'] == 4
assert s['new_constructors'] == 36 and s['definition_axiom_credit'] == 0
assert not s['coverage_producer_implemented']
runtime = BASE / s['runtime']
assert not runtime.exists(), 'Use a new runtime. Preserve all historical attempts.'
for name, record in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
overrides = json.loads((CONTROL / s['historical_overrides']).read_text())
stage = json.loads((ROOT / s['historical_overrides_stage']).read_text())
assert overrides == stage['baseline_overrides']


def verify_historical(name, record):
    path = ROOT / name
    digest = record['sha256'] if isinstance(record, dict) else record
    if path.exists() and SHA(path.read_bytes()) == digest:
        return verify(path, record)
    assert name in overrides, 'No Source68 BEFORE substitution: ' + name
    return verify(ROOT / overrides[name], record)


review_path = ROOT / s['candidate_Root_review_receipt']
assert str(review_path.relative_to(ROOT)) in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text())
review = json.loads(review_path.read_text())
assert review['manifest_sha256'] == s['components'][0]['manifest_sha256']
assert review['all_five_original_FIRSTs_byte_exact']
assert review['entire_current_Source68_Shared_prefix_exact_at_zero']
assert review['entire_610line_relation_append_and_36constructors_exact']
assert review['entire_done_leaf_and_proof_exact']
assert review['owning_axiom_reports'] == [0, 1] and review['owning_declaration_checks'] == [4, 0]
assert review['producer334c_unimplemented'] and review['whole_batch_theorem_credit'] == 0

prior = BASE / s['prior_work']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
publication = json.loads((ROOT / s['publication_verified_receipt']).read_text())
actual = json.loads((ROOT / s['publication_actual_receipt']).read_text())
push = json.loads((prior / 'PUSH-VERIFIED.json').read_text())
assert commit['source_commit'] == push['source_commit'] == s['source_commit']
assert commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert publication['actual_terminal'] and actual['actual_terminal']
assert publication['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert publication['actual_session'] == actual['actual_session'] == commit['publication_actual_session'] == s['publication_actual_session']
assert publication['runtime'] == s['prior_publication_runtime']
assert push['checkpoint_commit'] == push['remote_commit'] == s['checkpoint_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
assert not publication['joint_finite_completion_proved']
assert publication['source_files'] == s['source_files'] == 6287
assert publication['direct_audit_imports'] == 5287
assert publication['audited_theorems'] == commit['audited_theorems'] == s['prior_publication_audited_theorems']
assert [item['total_axiom_reports'] for item in publication['checks']] == s['prior_publication_gate_reports']
assert [item['declaration_checks'] for item in publication['checks']] == s['prior_publication_definition_checks']
assert push['archive_manifest_sha256'] == s['prior_archive_manifest_sha256']
assert push['source_tree_sha256'] == s['prior_source_tree_sha256']
verify(ROOT / s['prior_archive_manifest'], s['prior_archive_manifest_sha256'])

pubrun = BASE / s['prior_publication_runtime']
checked = json.loads((pubrun / 'checked.json').read_text())
assert checked == json.loads((pubrun / 'results.json').read_text())
assert checked['checks'] == publication['checks']
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in checked['checks'])
assert SHA((pubrun / 'checked.json').read_bytes()) == publication['checked_sha256']
pubpins = json.loads((pubrun / 'source-pins.json').read_text())
assert SHA((pubrun / 'source-pins.json').read_bytes()) == publication['source_pins_sha256']
assert len(pubpins) == publication['pins_independently_reverified'] == s['publication_pins']
for name, record in pubpins.items():
    verify_historical(name, record)
for key in ['prior_source68_private', 'prior_done_private']:
    info = s[key]
    record = json.loads((ROOT / info['verified_receipt']).read_text())
    actual = json.loads((ROOT / info['actual_receipt']).read_text())
    assert record['actual_terminal'] and actual['actual_terminal']
    assert record['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
    assert record['actual_session'] == actual['actual_session'] == info['actual']
    run = BASE / info['runtime']
    result = json.loads((run / 'checked.json').read_text())
    assert result == json.loads((run / 'results.json').read_text())
    assert result['checks'] == record['checks']
    assert [item['total_axiom_reports'] for item in result['checks']] == info['reports']
    assert [item['declaration_checks'] for item in result['checks']] == info['definition_checks']
    assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in result['checks'])
    assert SHA((run / 'checked.json').read_bytes()) == record['checked_sha256']
    pins = json.loads((run / 'source-pins.json').read_text())
    assert SHA((run / 'source-pins.json').read_bytes()) == record['source_pins_sha256']
    assert len(pins) == record['pins_independently_reverified'] == info['pins']
    for name, digest in pins.items():
        verify_historical(name, digest)

# Current compilation uses the actual published Source68, never a BEFORE snapshot.
subprocess.run(['git', 'merge-base', '--is-ancestor', s['source_commit'], 'HEAD'], cwd=ROOT, check=True)
subprocess.run(['git', 'diff', '--quiet', s['source_commit'], '--', 'lean/MicroCFTA',
    'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / s['source_baseline']).read_text())
normalpins = json.loads((prior / 'NORMAL-SOURCE-PINS.json').read_text())
assert baseline['source_commit'] == s['source_commit']
assert len(normalpins) == s['source_toolchain_pins'] == 6291
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == s['source_files'] == 6287
assert set(baseline['sources']) == {str(path.relative_to(ROOT)) for path in sources}
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert normalpins[name] == record['sha256']
raws = {}
fixtures = {}
for item in s['components']:
    packet = BASE / item['packet']
    candidate = json.loads(verify(packet / 'MANIFEST.json', item['manifest_sha256']))
    for name, record in candidate['files'].items():
        verify(packet / name, record)
    for filename in ['SOURCE-PINS.json', 'DEPENDENCY-PINS.json', 'ROOT-REVIEWS-AND-PRIOR-CHECK-PINS.json']:
        pins = json.loads((packet / filename).read_text())
        for name, record in pins['files'].items():
            verify_historical(name, record)
    raw = verify(packet / item['source'], item['raw'])
    if item['new_module']:
        assert not (ROOT / 'lean/MicroCFTA' / item['source']).exists(), 'New module collision.'
        added = raw
        assert raw == (BASE / '20261118-stored-universe-done-output-assignment-proof-draft' / item['source']).read_bytes()
    else:
        old = verify(ROOT / item['old_owner_source'], item['old_owner'])
        added = verify(packet / item['append'], item['append_sha256'])
        assert item['old_owner_offset'] == 0 and raw == old + added
        assert added == (BASE / '20261118-full-result-eager-query-coverage-relations-entry-repair-rebase/APPEND.lean.txt').read_bytes()
        assert len(added.splitlines()) == 610
        assert len(re.findall(rb'^private inductive ', added, re.M)) == 4
        assert not re.search(rb'^(?:private )?theorem ', added, re.M)
    for header in item['headers']:
        data = verify(packet / header['file'], header)
        assert raw.count(data) == 1
    assert not re.search(rb'\b(?:sorry|axiom)\b', added)
    assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', added)
    fixture = verify(CONTROL / item['fixture'], item['fixture_sha256'])
    assert re.findall(r'^#check (\S+)', fixture.decode(), re.M) == item['definition_qnames']
    assert re.findall(r'^#print axioms (\S+)', fixture.decode(), re.M) == item['private_qnames'] + item['public_qnames']
    raws[item['module']] = raw
    fixtures[item['module']] = fixture
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
assert graph == topo['direct_imports'] and order == topo['topological_order']
assert len(order) == s['expected_total_modules'] == 2876
assert len(seen - set(raws)) == s['expected_normal_dependencies'] == 2874
assert [name for name in order if name in raws] == s['compile_order']
normalobjects = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
for name in seen - set(raws):
    assert (normalobjects / (name + '.olean')).is_file(), name
for filename in ['check-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((CONTROL / filename).read_text())

# Root starts mutation only after all read-only gates pass.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-query-coverage-relations-done-'))
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
    fixture = runtime / 'source/MicroCFTA' / item['source']
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
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'commands': 2,
    'public_axiom_reports': 1, 'private_axiom_reports': 0, 'definition_checks': 4,
    'definition_axiom_credit': 0, 'normal_Source_changed': False}))
