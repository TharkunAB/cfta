import hashlib
import json
import subprocess
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-dispatch-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-dispatch'
previous = 'bb9e8d80b3fc9504a2211cdac5861de4f0a39adf'
destination = 'git@github.com:TharkunAB/cfta.git'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)

spec = json.loads((area / 'publication-spec.json').read_text())
head = git('rev-parse', 'HEAD').decode().strip()
assert head == spec['head']
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert git('remote', 'get-url', 'origin').decode().strip() == destination
assert git('remote', 'get-url', '--push', '--all', 'origin').decode().splitlines() == [destination]
assert not git('status', '--porcelain')
if sys.argv[1] == 'local':
    for line in (evidence / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        assert hashlib.sha256((evidence / name).read_bytes()).hexdigest() == digest, name
    indexed = {}
    for raw in git('ls-files', '--stage', '-z').split(b'\0'):
        if raw:
            metadata, name = raw.split(b'\t', 1)
            mode, blob, stage = metadata.decode().split()
            assert stage == '0'
            indexed[name] = (mode, blob)
    tree = {}
    for raw in git('ls-tree', '-r', '-z', 'HEAD').split(b'\0'):
        if not raw:
            continue
        metadata, name = raw.split(b'\t', 1)
        mode, kind, blob = metadata.decode().split()
        assert kind == 'blob'
        path = root / name.decode()
        data = path.read_bytes()
        assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
        assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
        tree[name] = (mode, blob)
    assert indexed == tree and len(tree) == spec['tracked_files']
    required = {evidence.relative_to(root).as_posix().encode() + b'/' + line.split('  ', 1)[1].encode()
                for line in (evidence / 'SHA256SUMS').read_text().splitlines()}
    required.add((evidence / 'SHA256SUMS').relative_to(root).as_posix().encode())
    assert required <= set(tree), sorted(required - set(tree))
    commits = git('rev-list', '--reverse', previous + '..HEAD').decode().splitlines()
    assert commits == spec['commits']
    report = dict(status='PASS', head=head, previous=previous, destination=destination,
                  commits=commits, tracked_files=len(tree), index_equals_tree_equals_files=True,
                  clean=True, evidence_manifest='PASS', goal='ACTIVE_INCOMPLETE')
    (area / 'local-publication.json').write_text(json.dumps(report, indent=2) + '\n')
else:
    assert sys.argv[1] == 'push'
    assert json.loads((area / 'local-publication.json').read_text())['head'] == head
    command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
               '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential']
    def remote(ref='refs/heads/formalize'):
        return subprocess.check_output(command + ['ls-remote', '--exit-code', 'origin', ref],
                                       cwd=root, timeout=60).decode().split()[0]
    before = remote()
    assert before in [previous, head], before
    if before != head:
        result = subprocess.run(command + ['push', 'origin', 'HEAD:refs/heads/formalize'],
                                cwd=root, capture_output=True, timeout=60)
        (area / 'push.log').write_bytes(result.stdout + result.stderr)
        assert result.returncode == 0, (result.stdout + result.stderr).decode()
    after = remote()
    assert after == head and not git('status', '--porcelain')
    report = dict(status='PUSHED_AND_REMOTE_VERIFIED', destination=destination,
                  ref='refs/heads/formalize', previous_remote=before, remote_head=after, remote_main=remote('refs/heads/main'),
                  clean=True, goal='ACTIVE_INCOMPLETE')
    (area / 'remote-publication.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
