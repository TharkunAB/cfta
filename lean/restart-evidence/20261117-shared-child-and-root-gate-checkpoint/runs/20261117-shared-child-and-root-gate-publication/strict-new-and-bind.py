from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
prior = root / 'lean/restart-evidence/20261117-selected-row-and-prefix-publication'
archive = root / 'lean/restart-evidence/20261117-selected-row-and-prefix-checkpoint'
work = root / 'lean/restart-evidence/20261117-shared-child-and-root-gate-work'
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
print(json.dumps({'inherited_component_reports_verified': 374,
                  'fresh_component_reports_expected': 3,
                  'old_sources_and_toolchain_byte_exact': True}), flush=True)
commands = [['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-shared-child-and-root-gate-publication/source', '-o', '/tmp/mcfta-source-child-gate-publication-5coap9w0/SourceSynthesisSharedProgramChildMarkBirth.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-shared-child-and-root-gate-publication/source/MicroCFTA/SourceSynthesisSharedProgramChildMarkBirth.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-shared-child-and-root-gate-publication/source', '-o', '/tmp/mcfta-source-child-gate-publication-5coap9w0/SourceSynthesisCurrentRootEmptyCheckGate.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-shared-child-and-root-gate-publication/source/MicroCFTA/SourceSynthesisCurrentRootEmptyCheckGate.lean']]
for command in commands:
    subprocess.run(command, check=True)
