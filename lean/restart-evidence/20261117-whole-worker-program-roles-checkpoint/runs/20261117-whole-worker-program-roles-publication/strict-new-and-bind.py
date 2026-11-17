from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
prior = root / 'lean/restart-evidence/20261117-actual-eager-role-producer-publication'
archive = root / 'lean/restart-evidence/20261117-actual-eager-role-producer-checkpoint'
work = root / 'lean/restart-evidence/20261117-whole-worker-program-roles-work'
sha = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
preflight = json.loads((runtime / 'OWNER-FRESH-PREFLIGHT.json').read_text())
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit_name = 'lean/MicroCFTA/Audit.lean'
fragment_name = 'lean/MicroCFTA/SourceSynthesisActualEagerProgramFragmentRoles.lean'
before_owner = (work / 'SourcePruningEnumerationSharedEagerReservation-BEFORE.lean.txt').read_bytes()
before_audit = (work / 'Audit-BEFORE.lean.txt').read_bytes()
before_fragment = (work / 'SourceSynthesisActualEagerProgramFragmentRoles-BEFORE.lean.txt').read_bytes()
preflight_audit = (work / 'AUDIT-PREFLIGHT.lean.txt').read_bytes()
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
old = {owner_name: before_owner, audit_name: before_audit, fragment_name: before_fragment}
for name, digest in json.loads((prior / 'source-pins.json').read_text()).items():
    data = old[name] if name in old else (root / name).read_bytes()
    assert sha(data) == digest, name
for name, digest in preflight['artifacts'].items():
    assert sha((root / name).read_bytes()) == digest, name
check = root / 'lean/restart-evidence' / preflight['check']
result = json.loads((check / 'checked.json').read_text())
assert result['owner_append_checked'] and all(result['passed'])
assert len(result['checks']) == 2 and result['checks'][1]['total_axiom_reports'] == 264
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           for c in result['checks'])
owner = (root / owner_name).read_bytes()
assert sha(owner) == preflight['normal_owner_sha256'] == preflight['assembled_sha256']
assert sha(before_owner) == preflight['old_owner_sha256']
offset = preflight['old_owner_offset']
assert owner[offset:offset + len(before_owner)] == before_owner
fragment = (root / fragment_name).read_bytes()
assert sha(fragment) == preflight['normal_fragment_sha256'] and fragment.startswith(before_fragment)
owner_selection = json.loads((check / 'selection.json').read_text())
assert owner_selection['assembled_sha256'] == sha(owner)
assert owner_selection['reports'] == 264 and owner_selection['previous_owner_reports'] == 252
assert owner_selection['new_private_reports'] == 12
assert owner_selection['old_owner_bytes'] == len(before_owner) == 2446450
old_probes = (work / 'PreviousOwnerProbes252.lean.txt').read_bytes()
proof = (check / 'source/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes()
assert sha(proof) == preflight['proof_source_sha256']
assert proof.startswith(owner + b'\n' + old_probes)
assert old_probes.count(b'#print axioms ') == 252 and proof.count(b'#print axioms ') == 264
for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
    data = before_owner if name == owner_name else preflight_audit if name == audit_name else (root / name).read_bytes()
    assert sha(data) == digest, name
assert sha(preflight_audit) == preflight['preflight_audit_sha256']
output = (check / 'owner-and-appends.txt').read_text()
groups = [set(x.strip() for x in group.split(',') if x.strip())
          for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]
free = len(re.findall(r'does not depend on any axioms', output))
assert len(groups) + free == 264
assert not (set().union(*groups) - {'propext', 'Classical.choice', 'Quot.sound'})
assert 'sorryAx' not in output and not re.search(r': error(?:\(|:)', output)
assert selection['inherited_reports'] == 127
assert selection['fresh_owner_preflight_reports'] == 264
assert selection['fresh_strict_normal_reports'] == 14
print(json.dumps({'inherited_reports_verified': 127, 'fresh_owner_reports_verified_this_batch': 264,
    'actual_fresh_strict_reports_expected': 14, 'owner_recompiled_here': False}), flush=True)

commands = [['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-whole-worker-program-roles-publication/source', '-o', '/tmp/mcfta-whole-role-publication-0gyh0tn8/SourceSynthesisObservedChildProgramSlots.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-whole-worker-program-roles-publication/source/MicroCFTA/SourceSynthesisObservedChildProgramSlots.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-whole-worker-program-roles-publication/source', '-o', '/tmp/mcfta-whole-role-publication-0gyh0tn8/SourceSynthesisActualEagerProgramFragmentRoles.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261117-whole-worker-program-roles-publication/source/MicroCFTA/SourceSynthesisActualEagerProgramFragmentRoles.lean']]
for command in commands:
    subprocess.run(command, check=True)
