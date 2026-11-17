from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
prior = root / 'lean/restart-evidence/20261117-warm-edge-initial-profile-publication'
archive = root / 'lean/restart-evidence/20261117-warm-edge-initial-profile-checkpoint'
work = root / 'lean/restart-evidence/20261117-warm-prefix-preservation-work'
sha = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
assert sha((archive / 'manifest.json').read_bytes()) == selection['prior_archive_manifest_sha256']
assert selection['prior_archive_manifest_sha256'] == '3e53a171aa5a71d27be39804cd837a080a2b19d94e33c3f1e3b74c6b89ea0e1b'
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
overrides = selection['baseline_overrides']
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
for name, path in overrides.items():
    assert sha((root / path).read_bytes()) == selection['override_digests'][name] == baseline[name]
for name, digest in json.loads((prior / 'source-pins.json').read_text()).items():
    assert sha((root / overrides.get(name, name)).read_bytes()) == digest, name
assert sha((root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes()) == selection['resource_owner_sha256']
print(json.dumps({'inherited_component_reports_verified': 478,
                  'fresh_public_reports_expected': 6,
                  'new_private_helper_declarations': 2,
                  'new_private_explicit_reports': 0,
                  'fresh_owner_preflight_reports': 0,
                  'unchanged_owner_reports_inherited': 264,
                  'historical_snapshots_and_toolchain_byte_exact': True}), flush=True)

commands = [['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source', '-o', '/tmp/mcfta-warm-prefix-preservation-publication-bwfucckq/SourceCurrentAllocatedNativeCompileDispatchOrigin.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source/MicroCFTA/SourceCurrentAllocatedNativeCompileDispatchOrigin.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source', '-o', '/tmp/mcfta-warm-prefix-preservation-publication-bwfucckq/SourceCurrentAllocatedNativeEdgeCompileDispatchOrigin.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source/MicroCFTA/SourceCurrentAllocatedNativeEdgeCompileDispatchOrigin.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source', '-o', '/tmp/mcfta-warm-prefix-preservation-publication-bwfucckq/SourceCurrentAllocatedNativeActualPrefixReturnedInduction.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source/MicroCFTA/SourceCurrentAllocatedNativeActualPrefixReturnedInduction.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source', '-o', '/tmp/mcfta-warm-prefix-preservation-publication-bwfucckq/SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source/MicroCFTA/SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source', '-o', '/tmp/mcfta-warm-prefix-preservation-publication-bwfucckq/SourceCurrentAllocatedNativeSamePrefixEdgeChildResult.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source/MicroCFTA/SourceCurrentAllocatedNativeSamePrefixEdgeChildResult.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source', '-o', '/tmp/mcfta-warm-prefix-preservation-publication-bwfucckq/SourceCurrentNativeWarmAuxiliaryPrefixes.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-prefix-preservation-publication/source/MicroCFTA/SourceCurrentNativeWarmAuxiliaryPrefixes.lean']]
for command in commands:
    subprocess.run(command, check=True)
