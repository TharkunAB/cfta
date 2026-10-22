import hashlib
import json
import subprocess
from pathlib import Path

R = Path('/home/tritlo/Code/mcfta')
H = R / 'lean/restart-evidence/20261022-original-row-edge-completion'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=R)

gate = json.loads((H / 'publication-gate.json').read_text())
proof = gate['proof_commit']
assert gate['status'] == 'ROOT_ACCEPTED'
assert proof == '26a01918be8b5a4b2232dbabe3d1ccb8b51a14da'
assert git('rev-parse', 'HEAD').decode().strip() == (H / 'proof-commit.txt').read_text().strip() == proof
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert git('remote', 'get-url', 'origin').decode().strip() == 'git@github.com:TharkunAB/cfta.git'
assert git('rev-parse', 'codex/backup-original-row-edge-completion-20261022-0246').decode().strip() == (H / 'starting-head.txt').read_text().strip()
assert git('rev-parse', 'main').decode().strip() == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
assert git('rev-parse', 'origin/main').decode().strip() == '794903b3fbad3becb8b28736fc33463760731fc7'
assert not git('diff', '--cached', '--name-only').strip()
subprocess.run(['/usr/bin/python3', str(H / 'verify-seal.py')], check=True)
files = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
         'lean/notes-current-system-claim.md', 'lean/notes-current-original-row-edge-completion.md']
subprocess.run(['git', 'diff', '--check', '--', *files], cwd=R, check=True)
subprocess.run(['git', 'add', '-f', '--', *files, str(H.relative_to(R))], cwd=R, check=True)
selected = git('diff', '--cached', '--name-only').decode().splitlines()
assert all(name in files or name.startswith(str(H.relative_to(R)) + '/') for name in selected)
index_names = set(git('ls-files', '-z').decode().split('\0'))
sealed_paths = 0
for manifest in (R / 'lean/restart-evidence').rglob('SHA256SUMS'):
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = R / name if name.startswith('lean/') else manifest.parent / name
        assert str(path.relative_to(R)) in index_names
        sealed_paths += 1
subprocess.run(['git', 'commit', '--quiet', '-m', 'Preserve original-row completion evidence and handoff'], cwd=R, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
assert not git('status', '--porcelain')
head_entries = {}
for raw in git('ls-tree', '-r', '-z', 'HEAD').split(b'\0'):
    if not raw:
        continue
    meta, name = raw.split(b'\t', 1)
    mode, kind, blob = meta.decode().split()
    assert kind == 'blob'
    path = R / name.decode()
    data = path.read_bytes()
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode
    head_entries[name.decode()] = (mode, blob)
index = {}
for raw in git('ls-files', '--stage', '-z').split(b'\0'):
    if not raw:
        continue
    meta, name = raw.split(b'\t', 1)
    mode, blob, stage = meta.decode().split()
    assert stage == '0'
    index[name.decode()] = (mode, blob)
assert index == head_entries
subprocess.run(['/usr/bin/python3', str(H / 'verify-seal.py')], check=True)
report = {'status': 'LOCAL_PASS', 'checkpoint': head, 'proof': proof,
          'filesystem_index_head_equal': True, 'tracked_blobs_and_modes': len(index),
          'all_sealed_paths_in_index': sealed_paths, 'clean': True,
          'publication': 'PENDING_FRESH_USER_APPROVAL_AFTER_AUTOMATIC_REVIEW_REJECTION',
          'destination': 'git@github.com:TharkunAB/cfta.git refs/heads/formalize',
          'network_commands_executed': 0, 'whole_goal': 'ACTIVE_AND_INCOMPLETE'}
Path('/tmp/mcfta-original-row-edge-completion-local-publication.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
