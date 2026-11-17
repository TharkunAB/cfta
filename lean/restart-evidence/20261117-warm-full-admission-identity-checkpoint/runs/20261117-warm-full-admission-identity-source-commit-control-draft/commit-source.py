from pathlib import Path
import datetime
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261117-warm-full-admission-identity-source-commit-control-draft'
WORK = BASE / '20261117-warm-full-admission-identity-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root must review and copy this controller into Work54.'
assert Path(__file__).read_bytes() == (CONTROL / 'commit-source.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
PARENT = 'c47d33f99209d27192a023bf2a9a0109f168333c'
MESSAGE = 'Classify retained warm calls and preserve entry identity across queries'
FILES = [
    'lean/MicroCFTA/SourceSynthesisCurrentUniverseWarmMuAdmission.lean',
    'lean/MicroCFTA/SourceCurrentAllocatedNativePastGammaEqualEntryPayload.lean',
    'lean/MicroCFTA/Audit.lean',
]

for name, record in json.loads((CONTROL / 'MANIFEST.json').read_text())['files'].items():
    assert SHA((CONTROL / name).read_bytes()) == record['sha256'], name
for name, record in json.loads((CONTROL / 'SOURCE-PINS.json').read_text()).items():
    data = (ROOT / name).read_bytes()
    assert SHA(data) == record['sha256'] and len(data) == record['bytes'], name
assert not (WORK / 'SOURCE-COMMIT.json').exists()
stage = json.loads((WORK / 'SOURCES-NORMAL-STAGING.json').read_text())
assert stage['prior_checkpoint'] == PARENT
assert {item['source_path'] for item in stage['components']} | {'lean/MicroCFTA/Audit.lean'} == set(FILES)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (4, 492, 496)
overrides = stage['baseline_overrides']
assert set(overrides) == set(FILES)
private = BASE / stage['private_run']
private_checked = json.loads((private / 'checked.json').read_text())
private_receipt = json.loads((WORK / 'PRIVATE-CHECK-VERIFIED.json').read_text())
assert private_receipt['actual_session'] == 72836
assert private_receipt['actual_terminal'] and private_receipt['actual_terminal_exit'] == 0
assert private_receipt['checks'] == private_checked['checks']
assert private_checked['two_owners_checked'] and all(private_checked['passed'])
assert private_checked['actual_new_public_axiom_reports'] == 4
assert private_checked['actual_definition_declaration_checks'] == 0
for name, digest in json.loads((private / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / overrides.get(name, name)).read_bytes()) == digest, name

publication = BASE / '20261117-warm-full-admission-identity-publication'
published = json.loads((publication / 'checked.json').read_text())
verified = json.loads((WORK / 'PUBLICATION-VERIFIED.json').read_text())
assert verified['actual_session'] == 54013
assert verified['actual_terminal'] and verified['actual_terminal_exit'] == 0
assert verified['run'] == publication.name
assert verified['checks'] == published['checks']
checks = published['checks']
assert len(checks) == 5
assert [item['name'] for item in checks] == [
    'public-build', 'strict-new-components-and-prior-bindings', 'independent-imports',
    'audit-build', 'audit-strict',
]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] for item in checks)
assert [item['total_axiom_reports'] for item in checks] == [702, 4, 297, 702, 702]
assert checks[1]['axiom_groups'] == 4 and checks[1]['axiom_free_reports'] == 0
assert checks[1]['declaration_checks'] == 0
assert checks[2]['axiom_groups'] == 294 and checks[2]['axiom_free_reports'] == 3
assert checks[4]['axiom_groups'] == 696 and checks[4]['axiom_free_reports'] == 6
assert published['all_five_gates_passed'] and published['source_pins_unchanged']
assert published['source_files'] == verified['source_files'] == 6267
assert published['audited_theorems'] == verified['audited_theorems'] == 100101
assert verified['pins_independently_reverified'] >= 6267
assert not published['joint_finite_completion_proved'] and not published['haskell_changed']
for name, digest in json.loads((publication / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
for item in stage['components']:
    current = (ROOT / item['source_path']).read_bytes()
    before = (ROOT / item['old_snapshot']).read_bytes()
    append = (BASE / item['packet'] / item['append']).read_bytes()
    assert SHA(current) == item['raw_sha256'] and current == before + append
old_audit = (WORK / 'Audit-BEFORE.lean.txt').read_bytes()
public_probes = (WORK / 'PUBLIC-PROBES.lean.txt').read_bytes()
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == old_audit + b'\n' + public_probes
assert (WORK / 'IMPORTS.lean.txt').read_bytes() == b''
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse', 'HEAD').decode().strip() == PARENT
assert not GIT('diff', '--cached', '--name-only')
assert set(GIT('diff', '--name-only', 'HEAD').decode().splitlines()) == set(FILES)
source_bytes = {name: (ROOT / name).read_bytes() for name in FILES}

# Root explicitly approves and executes this three-file Source commit.
subprocess.run(['git', 'add', '--', *FILES], check=True, cwd=ROOT)
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
    'message': MESSAGE, 'private_actual_session': 72836, 'publication_actual_session': 54013,
    'all_four_original_first_headers_exact': True, 'old_owner_prefixes_byte_exact': True,
    'all_six_cache_meanings_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False}
(WORK / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
