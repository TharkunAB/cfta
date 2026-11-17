from pathlib import Path
import datetime
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261117-third-query-six-seed-source-commit-control-draft'
WORK = BASE / '20261117-third-query-node-seed-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root must review and copy this controller into Work55.'
assert Path(__file__).read_bytes() == (CONTROL / 'commit-source.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
PARENT = 'c894b4e3fda56e1f8c275f02653f0bba3be7167a'
MESSAGE = 'Derive all cache seeds for the same third query history'
FILES = [
    'lean/MicroCFTA/SourceCurrentNativeAuxiliaryBaseKeyRecovery.lean',
    'lean/MicroCFTA/SourceCurrentNativeWarmBodyFirstInitialPayloads.lean',
    'lean/MicroCFTA/SourceCurrentNativeWarmCoherentInitialPayloads.lean',
    'lean/MicroCFTA/SourceSynthesisCurrentUniverseThirdQueryNodeSeed.lean',
    'lean/MicroCFTA/SourceSynthesisCurrentUniverseThirdQueryEdgeSeed.lean',
    'lean/MicroCFTA/SourceSynthesisCurrentUniverseThirdQuerySeeds.lean',
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
assert stage['prior_checkpoint'] == PARENT
assert {item['source_path'] for item in stage['components']} | {'lean/MicroCFTA/Audit.lean'} == set(FILES)
assert len(stage['components']) == 6 and len(FILES) == 7
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (7, 496, 503)
overrides = stage['baseline_overrides']
new_sources = {item['source_path'] for item in stage['components'] if item['kind'] == 'new_module'}
assert len(new_sources) == 3 and set(overrides) == set(FILES) - new_sources
private = BASE / stage['private_run']
private_checked = json.loads((private / 'checked.json').read_text())
private_receipt = json.loads((WORK / 'SIX-SEED-TOPOLOGICAL-REPAIR-VERIFIED.json').read_text())
assert private_receipt['actual_session'] == 37551
assert private_receipt['actual_terminal'] and private_receipt['actual_terminal_exit'] == 0
assert private_receipt['checks'] == private_checked['checks']
assert private_checked['all_six_components_checked'] and all(private_checked['passed'])
assert private_checked['actual_new_public_axiom_reports'] == 7
assert private_checked['actual_definition_declaration_checks'] == 0
assert private_checked['all_selected_first_headers_exact'] and private_checked['all_three_old_owner_prefixes_byte_exact']
for name, digest in json.loads((private / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / overrides.get(name, name)).read_bytes()) == digest, name

publication = BASE / '20261117-third-query-six-seed-publication'
published = json.loads((publication / 'checked.json').read_text())
verified = json.loads((WORK / 'PUBLICATION-VERIFIED.json').read_text())
assert verified['actual_session'] == 60614
assert verified['actual_terminal'] and verified['actual_terminal_exit'] == 0
assert verified['runtime'] == publication.name
assert verified['checks'] == published['checks']
checks = published['checks']
assert len(checks) == 5
assert [item['name'] for item in checks] == [
    'public-build', 'strict-new-components-and-prior-bindings', 'independent-imports',
    'audit-build', 'audit-strict',
]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['declaration_checks'] == 0 for item in checks)
assert [item['total_axiom_reports'] for item in checks] == [709, 7, 304, 709, 709]
assert checks[1]['axiom_groups'] == 7 and checks[1]['axiom_free_reports'] == 0
assert checks[2]['axiom_groups'] == 301 and checks[2]['axiom_free_reports'] == 3
assert checks[4]['axiom_groups'] == 703 and checks[4]['axiom_free_reports'] == 6
assert published['all_five_gates_passed'] and published['source_pins_unchanged']
assert published['source_files'] == verified['source_files'] == 6270
assert type(published['audited_theorems']) is int and published['audited_theorems'] > 0
assert published['audited_theorems'] == verified['audited_theorems']
assert verified['pins_independently_reverified'] == len(json.loads((publication / 'source-pins.json').read_text()))
assert not published['joint_finite_completion_proved'] and not published['haskell_changed']
assert published['all_six_third_query_cache_seeds_proved'] and published['exact_b4_joint_composition_checked']
for name, digest in json.loads((publication / 'source-pins.json').read_text()).items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
header_count = 0
probe_count = 0
for item in stage['components']:
    packet = BASE / item['packet']
    current = (ROOT / item['source_path']).read_bytes()
    assert current == (packet / item['source']).read_bytes()
    assert SHA(current) == item['raw_sha256']
    if item['kind'] == 'existing_owner_EOF':
        before = (ROOT / item['old_snapshot']).read_bytes()
        appended = (packet / item['append']).read_bytes()
        assert current == before + appended
        assert len(before) == item['old_bytes'] and SHA(before) == item['old_sha256']
    for header in item['headers']:
        data = (packet / header['file']).read_bytes()
        assert SHA(data) == header['sha256'] and data.rstrip(b'\n') in current
        header_count += 1
    probe = (packet / item['probe']).read_bytes()
    assert SHA(probe) == item['probe_sha256'] and b'#check ' not in probe
    probe_count += probe.count(b'#print axioms ')
assert header_count == probe_count == 7
old_audit = (WORK / 'Audit-BEFORE.lean.txt').read_bytes()
public_probes = (WORK / 'PUBLIC-PROBES.lean.txt').read_bytes()
imports = (WORK / 'IMPORTS.lean.txt').read_bytes()
assert len(old_audit) == 430643 and len(imports) == 195
assert imports.count(b'import ') == 3
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == imports + old_audit + b'\n' + public_probes
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse', 'HEAD').decode().strip() == PARENT
assert not GIT('diff', '--cached', '--name-only')
assert set(GIT('diff', '--name-only', 'HEAD').decode().splitlines()) == set(FILES) - new_sources
for name in new_sources:
    assert not GIT('ls-files', '--', name), name
source_bytes = {name: (ROOT / name).read_bytes() for name in FILES}
assert all(not (ROOT / name).is_symlink() for name in FILES)

# Root explicitly approves and executes this exact seven-file Source commit.
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
    'message': MESSAGE, 'private_actual_session': 37551, 'publication_actual_session': 60614,
    'audited_theorems': published['audited_theorems'],
    'all_seven_original_public_FIRST_headers_exact': True, 'all_three_old_owner_prefixes_byte_exact': True,
    'joint_middle_source_inventory_and_all_six_third_history_cache_seeds_proved': True,
    'arbitrary_independent_warm_query_sequence_proved': False, 'native_inhabitance_proved': False,
    'all_six_cache_meanings_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False}
(WORK / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
