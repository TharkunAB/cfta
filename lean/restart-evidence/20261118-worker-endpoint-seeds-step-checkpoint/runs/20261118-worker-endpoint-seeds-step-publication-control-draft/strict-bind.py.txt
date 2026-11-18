from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
RUNTIME = Path(__file__).resolve().parent
WORK = BASE/'20261118-worker-endpoint-seeds-step-work'
PRIOR = BASE/'20261118-worker-endpoint-seeds-zero-fixture-repair-publication'
ARCHIVE = BASE/'20261118-worker-endpoint-seeds-zero-checkpoint'
SHA = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((RUNTIME/'INHERITANCE-SELECTION.json').read_text())
assert SHA((ARCHIVE/'manifest.json').read_bytes()) == selection['prior_archive_manifest_sha256']
assert subprocess.check_output(['git','show',selection['prior_checkpoint']+':'+str((ARCHIVE/'manifest.json').relative_to(ROOT))],cwd=ROOT) == (ARCHIVE/'manifest.json').read_bytes()
subprocess.run(['python3',str(ARCHIVE/'verify.py')],check=True)
assert SHA((PRIOR/'checked.json').read_bytes()) == selection['prior_checked_sha256']
assert SHA((PRIOR/'source-pins.json').read_bytes()) == selection['prior_pins_sha256']
assert SHA((WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()) == selection['stage_sha256']
assert SHA((ROOT/selection['baseline_path']).read_bytes()) == selection['baseline_sha256']
for name,path in selection['baseline_overrides'].items():
    assert SHA((ROOT/path).read_bytes()) == selection['override_digests'][name]
for name,digest in json.loads((PRIOR/'source-pins.json').read_text()).items():
    assert SHA((ROOT/selection['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
assert selection['inherited_reports'] == 540 and selection['combined_reports'] == 545
assert selection['fresh_public_reports'] == 2 and selection['fresh_private_reports'] == 3
assert selection['new_private_theorems'] == 6 and selection['new_private_helpers_transitive'] == 3
assert selection['new_definitions'] == selection['definition_checks'] == selection['definition_axiom_credit'] == 0
assert selection['inherited_independent_checks'] == 300
assert selection['resource_owner_reports_inherited'] == 264 and selection['fresh_credit_for_old_owner_theorems'] == 0
assert selection['rebuilt_Source65_leaf_and_zero_base_extra_credit'] == 0
assert len(selection['compile_order']) == len(set(selection['compile_order'])) == 3
print(json.dumps({'inherited_curated_reports_verified':540,'fresh_public_reports':2,'fresh_private_reports':3,
    'unqueried_growth_helpers':3,'new_definitions':0,'strict_owning_module_rebuilds':3,'fresh_old_owner_credit':0}),flush=True)
for module in selection['compile_order']:
    subprocess.run(['lake','env','python3',str(RUNTIME/'shadow-compile.py'),module],check=True)
