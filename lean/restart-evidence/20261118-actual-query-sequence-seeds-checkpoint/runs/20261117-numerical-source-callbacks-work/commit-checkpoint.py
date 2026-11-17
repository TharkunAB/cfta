from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
packet = root / 'lean/restart-evidence/20261118-actual-query-sequence-seeds-checkpoint'
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
source = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == source
subprocess.run(['python3', str(packet / 'verify.py'), '--current-tree'], check=True)
assert not git('diff', '--cached', '--name-only')
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']
assert set(git('diff', '--name-only').decode().splitlines()) == set(documents)
names = documents + [str(p.relative_to(root)) for p in sorted(packet.rglob('*')) if p.is_file()]
assert all(not (root / name).is_symlink() for name in names)
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Record admitted native query sequence invariants and remaining worker gaps'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
assert not git('status', '--porcelain', '--untracked-files=no')
receipt = {'checkpoint_commit': head, 'source_commit': source,
           'packet': str(packet.relative_to(root)), 'committed_files': len(names),
           'all_current_archive_and_document_checks_passed': True,
           'joint_finite_completion_proved': False, 'goal_active': False,
           'work_authorized_by_explicit_user_resume': True, 'persistent_goal_control_status': 'paused',
           'goal_completion_claimed': False}
(work / 'CHECKPOINT-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
