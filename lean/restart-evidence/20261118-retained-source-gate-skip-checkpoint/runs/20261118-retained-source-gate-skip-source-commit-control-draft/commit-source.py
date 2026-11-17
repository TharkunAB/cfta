from pathlib import Path
import datetime
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-retained-source-gate-skip-source-commit-control-draft'
WORK = BASE / '20261118-retained-source-gate-skip-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root must review and copy this controller into Work57.'
assert Path(__file__).read_bytes() == (CONTROL / 'commit-source.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
PARENT = 'df5c56125ad1296586afcd35b1cc75010f583d5b'
MESSAGE = 'Preserve source descendant gates through retained shared checks'
FILES = [
    'lean/MicroCFTA/SourceSynthesisCurrentRootEmptyCheckGate.lean',
    'lean/MicroCFTA/SourceSynthesisCurrentRetainedSharedEmptySkip.lean',
    'lean/MicroCFTA/Audit.lean',
]
for name, record in json.loads((CONTROL / 'MANIFEST.json').read_text())['files'].items():
    data = (CONTROL / name).read_bytes()
    assert SHA(data) == record['sha256'] and len(data) == record['bytes'], name
for name, record in json.loads((CONTROL / 'SOURCE-PINS.json').read_text()).items():
    data = (ROOT / name).read_bytes()
    assert SHA(data) == record['sha256'] and len(data) == record['bytes'], name
assert not (WORK / 'SOURCE-COMMIT.json').exists()
stage = json.loads((WORK / 'SOURCES-NORMAL-STAGING.json').read_text())
assert {item['source_path'] for item in stage['components']} | {'lean/MicroCFTA/Audit.lean'} == set(FILES)
assert len(stage['components']) == 2
assert (stage['source_files'], stage['audit_imports'], stage['audit_reports'], stage['independent_reports']) == (6279, 5279, 726, 321)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (2, 518, 520)
assert stage['new_private_theorems'] == stage['new_prop_definitions'] == 0
assert stage['resource_owner_reports_inherited'] == 264 and stage['owner_preflight_reports_fresh_this_batch'] == 0
push = json.loads((ROOT / stage['prior_checkpoint_push_receipt']).read_text())
assert push['checkpoint_commit'] == push['remote_commit'] == PARENT
assert push['source_commit'] == stage['source_baseline'] == '1a3de82aec4bab8cc6b21012103e6311a951b266'
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
overrides = stage['baseline_overrides']
new_sources = {item['source_path'] for item in stage['components'] if item['kind'] == 'new_module'}
assert new_sources == {'lean/MicroCFTA/SourceSynthesisCurrentRetainedSharedEmptySkip.lean'}
assert set(overrides) == set(FILES) - new_sources
baseline = json.loads((WORK / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6278 and len(set(baseline) - set(overrides)) == 6276
for name, digest in baseline.items():
    assert SHA((ROOT / overrides.get(name, name)).read_bytes()) == digest, name
assert {str(p.relative_to(ROOT)) for p in (ROOT / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | new_sources
private = BASE / stage['private_run']
private_receipt = json.loads((WORK / stage['private_verified_receipt']).read_text())
private_checked = json.loads((private / 'checked.json').read_text())
assert private_receipt['actual_session'] == 15994
assert private_receipt['actual_terminal'] and private_receipt['actual_terminal_exit'] == 0
assert private_receipt['checks'] == private_checked['checks'] and all(private_checked['passed'])
assert private_checked['two_components_checked'] and private_checked['proof_credit']
assert private_checked['actual_printed_public_axiom_reports'] == 2
assert private_checked['actual_definition_declaration_checks'] == 0
assert private_checked['both_selected_FIRST_headers_exact'] and private_checked['old_gate_owner_prefix_byte_exact']
for name, digest in json.loads((private / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / overrides.get(name, name)).read_bytes()) == digest, name

# These are final actual receipts. No transient publication receipt is frozen here.
publication = BASE / '20261118-retained-source-gate-skip-publication'
actual = json.loads((WORK / 'PUBLICATION-ACTUAL-RUN.json').read_text())
verified = json.loads((WORK / 'PUBLICATION-VERIFIED.json').read_text())
published = json.loads((publication / 'checked.json').read_text())
assert actual['actual_terminal'] and actual['actual_terminal_exit'] == 0
assert verified['actual_terminal'] and verified['actual_terminal_exit'] == 0
assert verified['runtime'] == actual['runtime'] == publication.name
assert type(verified['actual_session']) is int and verified['actual_session'] > 0
assert verified['actual_session'] == actual['actual_session']
assert verified['checks'] == published['checks']
assert json.loads((publication / 'results.json').read_text()) == published
assert verified['checked_sha256'] == SHA((publication / 'checked.json').read_bytes())
assert verified['source_pins_sha256'] == SHA((publication / 'source-pins.json').read_bytes())
checks = published['checks']
assert len(checks) == 5
assert [item['name'] for item in checks] == ['public-build',
    'strict-new-components-and-prior-bindings', 'independent-imports', 'audit-build', 'audit-strict']
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['declaration_checks'] == 0 for item in checks)
assert [item['total_axiom_reports'] for item in checks] == [726, 2, 321, 726, 726]
assert checks[1]['axiom_groups'] == 2 and checks[1]['axiom_free_reports'] == 0
assert checks[2]['axiom_groups'] == 318 and checks[2]['axiom_free_reports'] == 3
assert checks[4]['axiom_groups'] == 720 and checks[4]['axiom_free_reports'] == 6
assert published['all_five_gates_passed'] and published['source_pins_unchanged']
assert (published['source_files'], published['direct_audit_imports'], published['individual_reports'], published['independent_reports']) == (6279, 5279, 726, 321)
assert (published['fresh_reports'], published['inherited_reports'], published['combined_reports']) == (2, 518, 520)
assert published['source_retained_available_gate_proved'] and published['actual_shared_enabled_skip_proved']
assert published['fresh_credit_for_old_owner_theorems'] == 0
assert published['new_private_theorems'] == published['new_prop_definitions'] == 0
assert not published['joint_finite_completion_proved'] and not published['haskell_changed']
assert type(published['audited_theorems']) is int and published['audited_theorems'] > 0
assert published['audited_theorems'] == verified['audited_theorems']
pub_pins = json.loads((publication / 'source-pins.json').read_text())
assert verified['pins_independently_reverified'] == len(pub_pins)
for name, digest in pub_pins.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
for item in stage['components']:
    packet = BASE / item['packet']
    assert SHA((packet / 'MANIFEST.json').read_bytes()) == item['manifest_sha256']
    current = (ROOT / item['source_path']).read_bytes()
    assert current == (packet / item['source']).read_bytes() and SHA(current) == item['raw_sha256']
    if item['kind'] == 'existing_owner_EOF':
        before = (ROOT / item['old_snapshot']).read_bytes()
        assert len(before) == 5721 and SHA(before) == item['owner_sha256']
        assert current == before + (packet / item['append']).read_bytes()
    header = (packet / item['header']).read_bytes()
    assert SHA(header) == item['header_sha256']
    start = current.index(header.splitlines()[0])
    assert current[start:current.index(b' := by', start)].rstrip() == header.rstrip()
    probe = (packet / item['probe']).read_bytes()
    assert SHA(probe) == item['probe_sha256'] and probe.count(b'#print axioms ') == 1
old_audit = (WORK / 'Audit-BEFORE.lean.txt').read_bytes()
public_probes = (WORK / 'PUBLIC-PROBES.lean.txt').read_bytes()
imports = (WORK / 'IMPORTS.lean.txt').read_bytes()
assert len(old_audit) == 433976 and len(imports) == 63
assert old_audit.count(b'#print axioms ') == 724 and imports.count(b'import ') == 1
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == imports + old_audit + b'\n' + public_probes
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse', 'HEAD').decode().strip() == PARENT
assert not GIT('diff', '--cached', '--name-only')
assert set(GIT('diff', '--name-only', 'HEAD').decode().splitlines()) == set(FILES) - new_sources
for name in new_sources:
    assert not GIT('ls-files', '--', name), name
source_bytes = {name: (ROOT / name).read_bytes() for name in FILES}
assert all(not (ROOT / name).is_symlink() for name in FILES)

# Root explicitly approves and executes this exact three-file Source commit.
subprocess.run(['git', 'add', '-f', '--', *FILES], check=True, cwd=ROOT)
assert set(GIT('diff', '--cached', '--name-only').decode().splitlines()) == set(FILES)
for name, data in source_bytes.items():
    assert GIT('show', ':' + name) == data, name
subprocess.run(['git', 'diff', '--cached', '--check'], check=True, cwd=ROOT)
subprocess.run(['git', 'commit', '--quiet', '-m', MESSAGE], check=True, cwd=ROOT)
head = GIT('rev-parse', 'HEAD').decode().strip()
assert GIT('rev-parse', head + '^').decode().strip() == PARENT
assert set(GIT('diff-tree', '--no-commit-id', '--name-only', '-r', head).decode().splitlines()) == set(FILES)
assert not GIT('status', '--porcelain', '--untracked-files=no')
receipt = {'at': datetime.datetime.now().astimezone().isoformat(), 'source_commit': head,
    'parent': PARENT, 'files': FILES, 'actual_terminal': True, 'actual_terminal_exit': 0,
    'message': MESSAGE, 'private_actual_session': private_receipt['actual_session'],
    'publication_actual_session': verified['actual_session'],
    'audited_theorems': published['audited_theorems'],
    'source_files': 6279, 'audit_imports': 5279, 'audit_reports': 726,
    'independent_reports': 321, 'fresh_public_reports': 2, 'inherited_reports': 518,
    'combined_reports': 520, 'resource_reports_inherited': 264,
    'both_public_FIRST_headers_exact': True, 'old_gate_owner_prefix_byte_exact': True,
    'old_audit_contiguous_block_preserved': True,
    'source_retained_available_gate_proved': True, 'actual_shared_enabled_skip_proved': True,
    'all_original_eager_worker_query_admissions_proved': False,
    'native_inhabitance_proved': False, 'guard_truth_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(WORK / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
