from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-all-outer-held-publication'
prior = 'd9ff58b10f739a1c7c3ea6b175c176a0bd91d754'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5 and report['all_history9374_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit_name = 'lean/MicroCFTA/Audit.lean'
leaf = json.loads((work / 'LEAF-NORMAL-STAGING.json').read_text())
names = [owner_name, audit_name, leaf['source_path']]
assert set(git('diff', '--name-only').decode().splitlines()) == {owner_name, audit_name}
assert sha((root / leaf['source_path']).read_bytes()) == leaf['public_sha256'] == leaf['sha256']
old_owner = git('show', 'HEAD:' + owner_name)
old_audit = git('show', 'HEAD:' + audit_name)
receipt = json.loads((work / 'OWNER-NORMAL-STAGING.json').read_text())
new_owner = (root / owner_name).read_bytes()
offset = receipt['old_owner_offset']
assert sha(old_owner) == receipt['old_owner_sha256']
assert sha(new_owner) == receipt['assembled_sha256']
assert new_owner[offset:offset + len(old_owner)] == old_owner
assert (root / audit_name).read_bytes().split(b'\n', 1)[1].startswith(old_audit)
preserved = 0
for name, digest in json.loads((work / 'baseline-source-pins.json').read_text()).items():
    if name not in names:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6233
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Preserve causal held history and source arrow provenance'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'source_commit': head, 'parent': prior, 'files': names,
    'all_five_public_gates_passed': True, 'old_non_audit_non_owner_sources_byte_exact': preserved,
    'old_owner_bytes_preserved_contiguously': len(old_owner), 'old_owner_offset': offset,
    'all_old_owner_proof_bodies_and_limits_unchanged': True, 'old_audit_bytes_after_one_normal_import': True,
    'new_modules': 1, 'new_public_theorem_reports': 2, 'new_private_component_reports': 9,
    'original_source_arrow_staged_provenance_proved': True,
    'public9374_header_byte_exact': False, 'public9374_theorem_declaration_byte_exact': True,
    'historical_open_comment_removed': True, 'shared5e48_predicate_byte_exact': True,
    'same_original_runtime_fuels': True, 'all_history9374_proved': True,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
