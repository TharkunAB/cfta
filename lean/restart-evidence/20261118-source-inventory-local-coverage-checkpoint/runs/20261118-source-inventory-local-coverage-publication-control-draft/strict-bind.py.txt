from pathlib import Path
import hashlib
import json
import subprocess
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
RUNTIME = Path(__file__).resolve().parent
WORK = BASE/'20261118-source-inventory-local-coverage-work'
PRIOR = BASE/'20261118-query-coverage-relations-done-assignment-publication'
ARCHIVE = BASE/'20261118-query-coverage-relations-done-assignment-checkpoint'
SHA = lambda data: hashlib.sha256(data).hexdigest()
s = json.loads((RUNTIME/'INHERITANCE-SELECTION.json').read_text())
assert SHA((ARCHIVE/'manifest.json').read_bytes()) == s['prior_archive_manifest_sha256']
assert subprocess.check_output(['git','show',s['prior_checkpoint']+':'+str((ARCHIVE/'manifest.json').relative_to(ROOT))],cwd=ROOT) == (ARCHIVE/'manifest.json').read_bytes()
subprocess.run(['python3',str(ARCHIVE/'verify.py')],check=True)
assert SHA((PRIOR/'checked.json').read_bytes()) == s['prior_checked_sha256'] and SHA((PRIOR/'source-pins.json').read_bytes()) == s['prior_pins_sha256']
assert SHA((WORK/'SOURCES-NORMAL-STAGING.json').read_bytes()) == s['stage_sha256'] and SHA((ROOT/s['baseline_path']).read_bytes()) == s['baseline_sha256']
for name,path in s['baseline_overrides'].items():
    assert SHA((ROOT/path).read_bytes()) == s['override_digests'][name]
for name,digest in json.loads((PRIOR/'source-pins.json').read_text()).items():
    assert SHA((ROOT/s['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
assert (s['inherited_reports'],s['fresh_public_reports'],s['fresh_private_reports'],s['combined_reports']) == (564,2,2,568)
assert s['new_definitions'] == s['definition_checks'] == s['definition_axiom_credit'] == s['new_private_helpers_transitive'] == 0
assert s['definition_qnames'] == [] and s['new_constructors'] == 0
assert s['rebuilt_Source69_Prop_relations_and_36_constructors_extra_credit'] == s['rebuilt_Source69_generated_brecOn_extra_credit'] == s['old_generic_Mu_actual22743_additive_credit'] == 0
assert s['inherited_independent_checks'] == 300 and s['resource_owner_reports_inherited'] == 264
assert len(s['compile_order']) == len(set(s['compile_order'])) == 3
print(json.dumps(dict(inherited_curated_reports_verified=564,fresh_public_reports=2,fresh_private_reports=2,strict_owning_module_rebuilds=3,fresh_old_owner_credit=0)),flush=True)
for module in s['compile_order']:
    subprocess.run(['lake','env','python3',str(RUNTIME/'shadow-compile.py'),module],check=True)
