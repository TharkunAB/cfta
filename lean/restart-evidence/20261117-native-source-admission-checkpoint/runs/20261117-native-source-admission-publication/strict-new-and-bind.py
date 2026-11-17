from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
prior = root / 'lean/restart-evidence/20261117-whole-worker-program-roles-publication'
archive = root / 'lean/restart-evidence/20261117-whole-worker-program-roles-checkpoint'
work = root / 'lean/restart-evidence/20261117-native-source-admission-work'
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
assert sha((work / 'baseline-source-pins.json').read_bytes()) == selection['baseline_sha256']
assert sha((work / 'SOURCES-NORMAL-STAGING.json').read_bytes()) == selection['stage_sha256']
assert sha((work / 'AUDIT-BEFORE.lean.txt').read_bytes()) == selection['old_audit_sha256']
assert sha((work / 'KEYED-READER-OWNER-BEFORE.lean.txt').read_bytes()) == selection['old_reader_sha256']
for name, digest in json.loads((prior / 'source-pins.json').read_text()).items():
    if name == 'lean/MicroCFTA/Audit.lean':
        data = (work / 'AUDIT-BEFORE.lean.txt').read_bytes()
    elif name == 'lean/MicroCFTA/SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.lean':
        data = (work / 'KEYED-READER-OWNER-BEFORE.lean.txt').read_bytes()
    else:
        data = (root / name).read_bytes()
    assert sha(data) == digest, name
assert sha((root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes()) == selection['unchanged_resource_owner_sha256']
print(json.dumps({'inherited_component_reports_verified': 405,
                  'fresh_component_reports_expected': 38,
                  'fresh_owner_preflight_reports': 0,
                  'unchanged_owner_reports_inherited': 264,
                  'old_sources_and_toolchain_byte_exact': True}), flush=True)

commands = [['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-native-source-admission-publication/source', '-o', '/tmp/mcfta-native-admission-publication-xzma7cfb/SourceSynthesisCurrentUniverseNativeAllocation.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-native-source-admission-publication/source/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-native-source-admission-publication/source', '-o', '/tmp/mcfta-native-admission-publication-xzma7cfb/SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-native-source-admission-publication/source/MicroCFTA/SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.lean']]
for command in commands:
    subprocess.run(command, check=True)
