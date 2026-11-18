from pathlib import Path
import hashlib
import json
import subprocess
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
RUNTIME = Path(__file__).resolve().parent
WORK = BASE/'20261118-no-mu-native-inventory-work'
PRIOR = BASE/'20261118-source-inventory-local-coverage-publication'
ARCHIVE = BASE/'20261118-source-inventory-local-coverage-checkpoint'
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
assert (s['inherited_reports'],s['fresh_public_reports'],s['fresh_private_reports'],s['combined_reports']) == (568,1,0,569)
assert s['inherited_independent_checks'] == 300 and s['resource_owner_reports_inherited'] == 264
assert len(s['compile_order']) == 1
print(json.dumps(dict(inherited_curated_reports_verified=568,fresh_public_reports=1,fresh_private_reports=0,strict_owning_module_rebuilds=1)),flush=True)
subprocess.run(['lake','env','python3',str(RUNTIME/'shadow-compile.py'),s['compile_order'][0]],check=True)
