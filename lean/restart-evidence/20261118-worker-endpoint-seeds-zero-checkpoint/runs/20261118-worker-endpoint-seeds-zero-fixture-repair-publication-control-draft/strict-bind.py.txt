from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUNTIME = Path(__file__).resolve().parent
BASE = ROOT/'lean/restart-evidence'
WORK = BASE/'20261118-worker-endpoint-seeds-zero-work'
PRIOR = BASE/'20261118-invocation-native-query-projection-publication'
ARCHIVE = BASE/'20261118-invocation-native-query-projection-checkpoint'
SHA = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((RUNTIME/'INHERITANCE-SELECTION.json').read_text())
assert SHA((ARCHIVE/'manifest.json').read_bytes()) == selection['prior_archive_manifest_sha256']
committed = subprocess.check_output(['git','show',selection['prior_checkpoint']+':'+str((ARCHIVE/'manifest.json').relative_to(ROOT))],cwd=ROOT)
assert committed == (ARCHIVE/'manifest.json').read_bytes()
subprocess.run(['python3',str(ARCHIVE/'verify.py')],check=True)
assert SHA((PRIOR/'checked.json').read_bytes()) == selection['prior_checked_sha256']
assert SHA((PRIOR/'source-pins.json').read_bytes()) == selection['prior_pins_sha256']
assert SHA((WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()) == selection['stage_sha256']
assert SHA((ROOT/selection['baseline_path']).read_bytes()) == selection['baseline_sha256']
for name,path in selection['baseline_overrides'].items():
    assert SHA((ROOT/path).read_bytes()) == selection['override_digests'][name]
for name,digest in json.loads((PRIOR/'source-pins.json').read_text()).items():
    assert SHA((ROOT/selection['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
assert selection['fresh_public_reports'] == 0 and selection['fresh_private_reports'] == 2
assert selection['inherited_reports'] == 538 and selection['combined_reports'] == 540
assert selection['Prop_declaration_checks'] == 3 and selection['Prop_axiom_credit'] == 0
assert selection['resource_owner_reports_inherited'] == 264 and selection['fresh_credit_for_old_owner_theorems'] == 0
assert selection['rebuilt_prior_leaf_extra_credit'] == 0 and selection['new_private_helpers'] == 0
assert len(selection['compile_order']) == 1 and len(selection['private_qnames']) == 2 and len(selection['definition_names']) == 3
print(json.dumps({'inherited_curated_reports_verified':538,'fresh_private_reports_expected':2,
    'private_Prop_checks_expected':3,'definition_axiom_credit':0,'strict_owning_module_rebuilds':1,'fresh_old_resource_reports':0}),flush=True)
subprocess.run(['lake','env','python3',str(RUNTIME/'shadow-compile.py'),selection['compile_order'][0]],check=True)
