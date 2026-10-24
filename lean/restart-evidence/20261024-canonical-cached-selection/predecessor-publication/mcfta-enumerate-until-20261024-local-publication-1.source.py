import hashlib, json, subprocess, sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
head = 'c841846eba7ab893460375a99a34e1d3f27ee9b0'
previous = '790c39ce21f0be612fafcb6a36eb972ac5bf03f9'
destination = 'git@github.com:TharkunAB/cfta.git'
area = Path('/tmp/mcfta-enumerate-until-20261024')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse','HEAD').decode().strip() == head
assert git('branch','--show-current').decode().strip() == 'formalize'
assert not git('status','--porcelain')
assert git('remote','get-url','origin').decode().strip() == destination
if sys.argv[1] == 'local':
    target = area/'local-publication.json'
    assert not target.exists()
    index = {}
    for raw in git('ls-files','--stage','-z').split(b'\0'):
        if not raw:
            continue
        meta, name = raw.split(b'\t',1)
        mode, blob, stage = meta.decode().split()
        assert stage == '0'
        index[name.decode()] = (mode,blob)
    tree = {}
    for raw in git('ls-tree','-r','-z','HEAD').split(b'\0'):
        if not raw:
            continue
        meta, name = raw.split(b'\t',1)
        mode, kind, blob = meta.decode().split()
        assert kind == 'blob'
        path = root/name.decode()
        data = path.read_bytes()
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == blob, name
        assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
        tree[name.decode()] = (mode,blob)
    assert index == tree and len(tree) == 126520
    commits = git('rev-list','--reverse',previous+'..HEAD').decode().splitlines()
    assert commits == ['ecabbf38e669d96275ce991fa8a843bcec3b51ed',head]
    report = dict(status='PASS', head=head, previous=previous, destination=destination,
                  commits=commits, tracked_files=len(tree), index_equals_tree_equals_files=True,
                  tree=git('rev-parse','HEAD^{tree}').decode().strip(), clean=True)
    target.write_text(json.dumps(report, indent=2)+'\n')
else:
    assert sys.argv[1] == 'push'
    assert json.loads((area/'local-publication.json').read_text())['head'] == head
    command = ['git','-c','url.https://github.com/.insteadOf=git@github.com:',
               '-c','credential.helper=', '-c','credential.helper=!/snap/bin/gh auth git-credential']
    def remote():
        return subprocess.check_output(command+['ls-remote','--exit-code','origin','refs/heads/formalize'],
                                       cwd=root,timeout=60).decode().split()[0]
    before = remote()
    assert before in [previous,head], before
    if before != head:
        result = subprocess.run(command+['push','origin','HEAD:refs/heads/formalize'],
                                cwd=root,capture_output=True,timeout=60)
        (area/'push.log').write_bytes(result.stdout+result.stderr)
        assert result.returncode == 0, (result.stdout+result.stderr).decode()
    after = remote()
    assert after == head and not git('status','--porcelain')
    report = dict(status='PUSHED_AND_REMOTE_VERIFIED', destination=destination,
                  ref='refs/heads/formalize', previous_remote=before, remote_head=after,
                  head=head, clean=True, goal='ACTIVE_INCOMPLETE')
    (area/'remote-publication.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
