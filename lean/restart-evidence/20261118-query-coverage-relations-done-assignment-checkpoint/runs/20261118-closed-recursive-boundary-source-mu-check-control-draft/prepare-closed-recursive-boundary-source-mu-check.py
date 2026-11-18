from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-closed-recursive-boundary-source-mu-check-control-draft'
WORK = BASE / '20261118-closed-recursive-boundary-source-mu-check-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root copies the frozen preparer into fresh Work.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-closed-recursive-boundary-source-mu-check.py').read_bytes()
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
assert manifest['status'] == 'FROZEN PRIVATE CHECK CONTROLLER / NOT EXECUTED', 'Root must freeze the OPEN draft.'
for name, record in manifest['files'].items():
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
selection = json.loads((CONTROL / 'SELECTION.json').read_text())
assert selection['status'] == 'FROZEN PRIVATE CHECK CANDIDATE / NOT EXECUTED'
assert selection['work'] == WORK.name
assert selection['runtime'] == '20261118-closed-recursive-boundary-source-mu-private-check'
assert selection['source_commit'] == '050660aa22418bdf3f99e7a38d97e0ad7dc60369'
assert selection['verified_prior_checkpoint_commit'] == '9a83c5c58a34cb34a28065887ba23e3025767304'
assert selection['normal_baseline_mode'] == 'PUBLISHED_SOURCE68'
assert selection['source_files'] == 6287 and selection['private_shadow_source_files'] == 6288
assert selection['expected_checks'] == len(selection['components']) == 1
assert selection['expected_total_axiom_reports'] == selection['expected_public_axiom_reports'] == 1
assert selection['expected_explicit_private_axiom_reports'] == selection['new_private_theorems'] == 0
assert selection['expected_declaration_checks'] == selection['new_definitions'] == 0
assert selection['new_private_helpers_transitive'] == 0 and selection['outside_Source68_and_Source69_selected_batches']
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Preserve prior runtimes; choose a fresh namespace.'
receipt_pins = json.loads((CONTROL / 'RECEIPT-PINS.json').read_text())
for name, record in receipt_pins.items():
    verify(ROOT / name, record)
prior = BASE / selection['prior_work']
publication = BASE / selection['prior_publication_runtime']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
receipt = json.loads((ROOT / selection['publication_verified_receipt']).read_text())
actual = json.loads((ROOT / selection['publication_actual_receipt']).read_text())
checked = json.loads((publication / 'checked.json').read_text())
assert selection['publication_verified_receipt'].endswith('/IMPORT-REPAIR-PUBLICATION-VERIFIED.json')
assert selection['publication_actual_receipt'].endswith('/IMPORT-REPAIR-PUBLICATION-ACTUAL-RUN.json')
assert commit['source_commit'] == selection['source_commit']
assert commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert commit['publication_actual_session'] == receipt['actual_session'] == actual['actual_session'] == selection['prior_publication_actual_session'] == 32291
assert receipt['actual_terminal'] and actual['actual_terminal']
assert receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert receipt['runtime'] == actual['runtime'] == publication.name
assert checked == json.loads((publication / 'results.json').read_text())
assert checked['checks'] == receipt['checks']
assert SHA((publication / 'checked.json').read_bytes()) == receipt['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == receipt['source_pins_sha256']
assert [item['total_axiom_reports'] for item in checked['checks']] == selection['prior_publication_gate_reports'] == [748, 3, 343, 748, 748]
assert [item['declaration_checks'] for item in checked['checks']] == selection['prior_publication_declaration_checks'] == [0, 0, 0, 0, 0]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in checked['checks'])
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert receipt['source_files'] == 6287 and receipt['direct_audit_imports'] == 5287
assert receipt['audited_theorems'] == commit['audited_theorems'] == selection['prior_publication_audited_theorems'] == 100297
publication_pins = json.loads((publication / 'source-pins.json').read_text())
assert len(publication_pins) == receipt['pins_independently_reverified'] == selection['prior_publication_pins_reverified'] == 10829
for name, record in publication_pins.items():
    verify(ROOT / name, record)
push = json.loads((ROOT / selection['prior_push_verified_receipt']).read_text())
assert push['source_commit'] == selection['source_commit']
assert push['checkpoint_commit'] == push['remote_commit'] == selection['verified_prior_checkpoint_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
assert push['normal_Source_files'] == 6287 and push['publication_actual_session'] == 32291
assert push['source_tree_sha256'] == selection['prior_source_tree_sha256']
assert push['archive_manifest_sha256'] == selection['prior_archive_manifest_sha256'] == '962847ae49864161c33f3fd690289d72be00a97a1531295e30d9771afee263ba'
verify(ROOT / selection['prior_archive_manifest'], selection['prior_archive_manifest_sha256'])
assert not push['joint_finite_completion_proved']
assert selection['Source69_results_required'] is False
assert selection['Root_schedule_after_actual_session_terminal'] == 7991
assert selection['Root_schedule_before_normal_Source69_staging']

packet = BASE / selection['candidate_packet']
candidate_manifest = json.loads(verify(packet / 'MANIFEST.json', selection['candidate_manifest_sha256']))
assert selection['candidate_manifest_sha256'] == '8a41db6a046771dbec9893e23203fca03903bd0bd5377780e3a50097c3ea3d7c'
assert len(candidate_manifest['files']) == selection['expected_candidate_artifacts'] == 11
for name, record in candidate_manifest['files'].items():
    verify(packet / name, record)
candidate_pins = json.loads((packet / 'SOURCE-PINS.json').read_text())
assert candidate_pins['normal_source_files_observed'] == selection['source_files']
assert len(candidate_pins['files']) == selection['expected_candidate_source_pins'] == 238
for name, record in candidate_pins['files'].items():
    verify(ROOT / name, record)
review = json.loads((ROOT / selection['Root_mathematical_review']).read_text())
assert review['status'] == 'FINAL ROOT GENERIC SOURCE MU CUT REVIEW; UNCOMPILED ZERO CREDIT'
assert review['manifest_sha256'] == selection['candidate_manifest_sha256']
assert review['artifacts_verified'] == 11 and review['pins_independently_reverified'] == 238
assert review['original_816byte_FIRST_exact'] and review['full_39line_proof_read']
assert review['generic_ordinaryEdges_eq_owning_law_read']
assert review['actual_Mu_residency_and_NoNewMu_source_record_used']
assert review['closed_union_flat_nonempty_and_irreducibility_argument']
assert review['new_helpers_definitions_or_premises'] == 0 and review['new_public_theorems'] == 1
assert review['not_every_source_assumed_to_have_Mu'] and review['Done_generalization_not_implemented']
assert not review['compiled'] and review['proof_credit'] == 0 and review['outside_Source68_and_Source69_selected_batches']
assert not review['guard_truth_and_joint_root_completion_proved'] and not review['haskell_changed']

# Root executes these read-only Git gates only after freezing this controller.
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', selection['source_commit'], 'HEAD'], cwd=ROOT, check=True)
changes = subprocess.check_output(['git', 'diff', '--name-only', selection['source_commit'], 'HEAD'], cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md'] or name.startswith('lean/restart-evidence/') for name in changes), changes
subprocess.run(['git', 'diff', '--quiet', selection['source_commit'], '--', 'lean/MicroCFTA', 'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / selection['source_baseline']).read_text())
normal_pins = json.loads((ROOT / baseline['normal_source_pins']).read_text())
assert baseline['source_commit'] == selection['source_commit'] and baseline['source_files'] == 6287
assert len(normal_pins) == baseline['all_normal_source_and_toolchain_pins'] == 6291
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
normal_names = {name for name in normal_pins if name.startswith('lean/MicroCFTA/')}
assert len(sources) == len(normal_names) == 6287
assert {str(path.relative_to(ROOT)) for path in sources} == normal_names
for name, digest in normal_pins.items():
    verify(ROOT / name, digest)

item = selection['components'][0]
assert item['module'] == 'SourceCurrentClosedRecursiveBoundaryMuOrigin'
assert item['new_module'] and not (ROOT / 'lean/MicroCFTA' / item['source']).exists()
raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
assert item['raw_sha256'] == '9d2f8c9657fb3d070992e7524642215791c4beb8c850abc88c69d982f3dad685'
assert len(re.findall(rb'^theorem ', raw, re.M)) == 1
assert not re.search(rb'^private theorem ', raw, re.M)
assert not re.search(rb'^(?:private )?(?:noncomputable )?(?:def|abbrev|opaque|inductive|structure) ', raw, re.M)
assert not re.search(rb'\b(?:sorry|axiom)\b', raw)
assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', raw)
assert b'#print axioms ' not in raw and b'#check ' not in raw
header = verify(packet / item['header'], item['header_sha256'])
proof = verify(packet / item['proof'], item['proof_sha256'])
if raw.count(header) != 1:
    assert header.endswith(b'\n') and raw.count(header[:-1]) == 1
    offset = raw.index(header[:-1]) + len(header) - 1
    assert raw[offset:].startswith(b' := by\n')
assert raw.count(proof) == 1
probe = verify(CONTROL / item['probe'], item['probe_sha256'])
assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['public_qnames']
assert probe.count(b'#print axioms ') == 1 and b'#check ' not in probe

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
closure = json.loads((packet / 'IMPORT-CLOSURE.json').read_text())
assert not closure['cycles'] and closure['new_module_name_absent'] and closure['fresh_outputs'] == [item['module']]
assert graph == closure['direct_imports'] and order == closure['full_transitive_order']
assert len(order) == closure['total_modules'] == selection['expected_total_transitive_modules'] == 233
assert len(seen - {item['module']}) == closure['normal_dependencies'] == selection['expected_normal_dependency_modules'] == 232
assert [name for name in order if name == item['module']] == selection['compile_order']
normal_objects = ROOT / baseline['normal_objects']
for name in seen - {item['module']}:
    obj = normal_objects / (name + '.olean')
    assert obj.is_file() and obj.resolve().parent == normal_objects.resolve(), str(obj)
for name in ['shadow-compile.py.txt', 'check-driver.py.txt']:
    ast.parse((CONTROL / name).read_text())

# Root starts fresh runtime/object mutations only after every read-only gate passes.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-closed-recursive-boundary-source-mu-'))
(objects / 'MicroCFTA').mkdir()
linked = []
for obj in sorted(normal_objects.glob('*.olean')):
    if obj.stem in paths and obj.stem != item['module']:
        assert obj.resolve().parent == normal_objects.resolve(), str(obj)
        (objects / 'MicroCFTA' / obj.name).symlink_to(obj)
        linked.append(obj.name)
assert item['module'] + '.olean' not in linked
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'shadow-imports.json').write_text(json.dumps({'linked_unchanged_modules': linked,
    'excluded_candidate_modules': [item['module']], 'candidate_output_links_created': False,
    'normal_dependency_modules': 232, 'cache_data_copied': False}, indent=2) + '\n')
fixture = runtime / 'source/MicroCFTA' / item['source']
fixture.parent.mkdir(parents=True, exist_ok=True)
fixture.write_bytes(raw + b'\n' + probe)
bound.add(fixture)
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2, sort_keys=True) + '\n')
(runtime / 'shadow-compile.py').write_bytes((CONTROL / 'shadow-compile.py.txt').read_bytes())
(runtime / 'check.py').write_bytes((CONTROL / 'check-driver.py.txt').read_bytes())
(runtime / 'NORMAL-STAGING-GATE.json').write_text(json.dumps({'source_commit': selection['source_commit'],
    'prior_Source68_push_receipt': selection['prior_push_verified_receipt'], 'checkpoint_commit': push['checkpoint_commit'],
    'private_check_requires_checkpoint_push': True, 'normal_Source_staging_executed_by_this_controller': False,
    'outside_Source68_and_Source69_selected_batches': True}, indent=2) + '\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)): SHA(path.read_bytes())
    for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'objects': str(objects), 'checks': 1,
    'expected_public_reports': 1, 'expected_private_reports': 0, 'new_definitions': 0,
    'normal_Source_changed': False, 'outside_Source68_and_Source69_selected_batches': True}))
