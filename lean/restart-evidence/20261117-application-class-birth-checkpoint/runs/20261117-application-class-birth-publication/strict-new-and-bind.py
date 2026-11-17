from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
prior = root / 'lean/restart-evidence/20261117-whole-branch-nested-held-publication'
archive = root / 'lean/restart-evidence/20261117-whole-branch-nested-held-checkpoint'
work = root / 'lean/restart-evidence/20261117-application-class-birth-work'
sha = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
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
for name, digest in json.loads((prior / 'source-pins.json').read_text()).items():
    data = (work / 'AUDIT-BEFORE.lean.txt').read_bytes() if name == 'lean/MicroCFTA/Audit.lean' else (root / name).read_bytes()
    assert sha(data) == digest, name
print(json.dumps({'inherited_component_reports_verified': 365,
                  'fresh_component_reports_expected': 1,
                  'old_sources_and_toolchain_byte_exact': True}), flush=True)
subprocess.run(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-application-class-birth-publication/source', '-o', '/tmp/mcfta-application-birth-publication-nuoa65fo/ApplicationClassBirth.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-application-class-birth-publication/source/MicroCFTA/SourceSynthesisApplicationClassBirth.lean'], check=True)
