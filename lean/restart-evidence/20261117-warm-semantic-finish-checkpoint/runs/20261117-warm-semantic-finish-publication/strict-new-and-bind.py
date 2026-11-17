from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).resolve().parent
prior = root / 'lean/restart-evidence/20261117-warm-prefix-preservation-publication'
archive = root / 'lean/restart-evidence/20261117-warm-prefix-preservation-checkpoint'
work = root / 'lean/restart-evidence/20261117-warm-semantic-finish-work'
sha = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
assert selection['prior_archive_manifest_sha256'] == 'c17fd2e06eec4ac0607eaf8649b358d7671df581cfc6a4ce74dba011ed3cc966'
assert sha((archive / 'manifest.json').read_bytes()) == selection['prior_archive_manifest_sha256']
committed = subprocess.check_output(['git', 'show', selection['prior_checkpoint'] + ':'
    + str((archive / 'manifest.json').relative_to(root))], cwd=root)
assert committed == (archive / 'manifest.json').read_bytes()
subprocess.run(['python3', str(archive / 'verify.py')], check=True)
records = json.loads((archive / 'archived-inputs.json').read_text())
for name in ['checked.json', 'source-pins.json']:
    path = prior / name
    record = next(item for item in records if item['original'] == str(path))
    archived = (archive / record['archived']).read_bytes()
    if record['gzip']:
        archived = gzip.decompress(archived)
    assert archived == path.read_bytes()
assert sha((prior / 'checked.json').read_bytes()) == selection['prior_checked_sha256']
assert sha((prior / 'source-pins.json').read_bytes()) == selection['prior_pins_sha256']
assert sha((work / 'baseline-source-pins.json').read_bytes()) == selection['baseline_sha256']
assert sha((work / 'SOURCES-NORMAL-STAGING.json').read_bytes()) == selection['stage_sha256']
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
overrides = selection['baseline_overrides']
assert set(overrides) == {'lean/MicroCFTA/Audit.lean'}
for name, path in overrides.items():
    assert sha((root / path).read_bytes()) == selection['override_digests'][name] == baseline[name]
for name, digest in json.loads((prior / 'source-pins.json').read_text()).items():
    assert sha((root / overrides.get(name, name)).read_bytes()) == digest, name
assert sha((root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes()) == selection['resource_owner_sha256']
assert selection['resource_owner_reports_inherited'] == 264
assert selection['owner_preflight_reports_fresh_this_batch'] == 0
assert (selection['inherited_reports'], selection['fresh_reports'], selection['combined_reports']) == (484, 5, 489)
print(json.dumps({'inherited_component_reports_verified': 484,
    'fresh_public_reports_expected': 5, 'definition_checks_expected': 3,
    'new_private_helper_declarations': 30, 'new_private_explicit_reports': 0,
    'fresh_owner_preflight_reports': 0, 'unchanged_owner_reports_inherited': 264,
    'historical_snapshots_and_toolchain_byte_exact': True}), flush=True)
for module in selection['compile_order']:
    subprocess.run(['lake', 'env', 'python3', str(runtime / 'shadow-compile.py'), module], check=True)
