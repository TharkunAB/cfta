exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
publication = load(Path('/tmp/mcfta-stored-node-counter-growth-local-publication.json'))
assert publication['status'] == 'LOCAL_PASS' and publication['filesystem_index_head_equal']
assert publication['clean'] and not git('status', '--porcelain')
checkpoint = git('rev-parse', 'HEAD').strip()
assert checkpoint == publication['checkpoint']
assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-list', '--count', START + '..HEAD').strip() == '2'
assert git('remote', 'get-url', 'origin').strip() == 'git@github.com:TharkunAB/cfta.git'
assert git('remote', 'get-url', '--push', 'origin').strip() == 'git@github.com:TharkunAB/cfta.git'
subprocess.run(['/usr/bin/python3', str(HERE / 'verify-seal.py')], cwd='/', check=True)
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
           '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential']
def remote_head():
    result = subprocess.check_output(command + ['ls-remote', 'origin', 'refs/heads/formalize'], cwd=ROOT, text=True)
    sha_value, reference = result.strip().split()
    assert reference == 'refs/heads/formalize'
    return sha_value
assert remote_head() == START
subprocess.run(command + ['push', 'origin', 'HEAD:refs/heads/formalize'], cwd=ROOT, check=True)
assert remote_head() == checkpoint
report_path = Path('/tmp/mcfta-stored-node-counter-growth-remote-publication.json')
assert not report_path.exists()
report = dict(status='PUSHED_AND_REMOTE_VERIFIED', branch='formalize',
    destination='git@github.com:TharkunAB/cfta.git', previous=START,
    checkpoint=checkpoint, proof=publication['proof'], commits=2,
    standing_explicit_user_authorization=True, goal_status='ACTIVE_INCOMPLETE')
report_path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
