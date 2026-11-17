from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).resolve().parent
work = root / 'lean/restart-evidence/20261117-numerical-source-callbacks-work'
prior = root / 'lean/restart-evidence/20261117-third-query-six-seed-publication'
archive = root / 'lean/restart-evidence/20261117-third-query-six-seed-checkpoint'
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()
assert selection['prior_archive_manifest_sha256'] == 'b581a4ad0fdb153f7388c0fb1b566d4b68a7dfcd810078361fec91000146fd1c'
assert sha((archive / 'manifest.json').read_bytes()) == selection['prior_archive_manifest_sha256']
committed = subprocess.check_output(['git', 'show', selection['prior_checkpoint'] + ':'
    + str((archive / 'manifest.json').relative_to(root))], cwd=root)
assert committed == (archive / 'manifest.json').read_bytes()
# This is a historical archive. The current tree has the newly staged sources.
subprocess.run(['python3', str(archive / 'verify.py')], check=True)
records = json.loads((archive / 'archived-inputs.json').read_text())
for name in ['checked.json', 'source-pins.json']:
    path = prior / name
    record = next(item for item in records if item['original'] == str(path))
    data = (archive / record['archived']).read_bytes()
    if record['gzip']:
        data = gzip.decompress(data)
    assert data == path.read_bytes()
assert sha((prior / 'checked.json').read_bytes()) == selection['prior_checked_sha256']
assert sha((prior / 'source-pins.json').read_bytes()) == selection['prior_pins_sha256']
assert sha((work / 'SOURCES-NORMAL-STAGING.json').read_bytes()) == selection['stage_sha256']
assert sha((work / 'SEED-CLOSURE-baseline-source-pins.json').read_bytes()) == selection['baseline_sha256']
for name, path in selection['baseline_overrides'].items():
    assert sha((root / path).read_bytes()) == selection['override_digests'][name]
for name, digest in json.loads((prior / 'source-pins.json').read_text()).items():
    assert sha((root / selection['baseline_overrides'].get(name, name)).read_bytes()) == digest, name
assert sha((root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes()) == selection['resource_owner_sha256']
assert selection['resource_owner_reports_inherited'] == 264
assert selection['owner_preflight_reports_fresh_this_batch'] == 0
assert (selection['inherited_reports'], selection['fresh_reports'], selection['combined_reports']) == (503, 15, 518)
assert len(selection['compile_order']) == 13 and len(set(selection['compile_order'])) == 13
assert selection['owning_private_reports_bound_separately'] == 2
assert selection['Prop_declaration_checks'] == 1 and selection['Prop_axiom_credit'] == 0
print(json.dumps({'inherited_component_reports_verified': 503,
    'fresh_public_reports_expected': 15, 'definition_checks_expected': 1,
    'strict_module_rebuilds': 13, 'private_helpers_compiled': 10,
    'private_owning_reports_bound_separately': 2, 'fresh_resource_owner_reports': 0,
    'unchanged_resource_owner_reports_inherited': 264}), flush=True)
for module in selection['compile_order']:
    subprocess.run(['lake', 'env', 'python3', str(runtime / 'shadow-compile.py'), module], check=True)
# Public queries use the same freshly rebuilt namespace. The private two-report
# fixture stays in the verified private-check receipt and never enters Audit.
subprocess.run(['lake', 'env', 'python3', str(runtime / 'shadow-compile.py'),
    '--public-probes'], check=True)
