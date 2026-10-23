exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
proposal = Path('/tmp/mcfta-cluster-admission-closing-progress.md')
assert sha(proposal) == '9038c5a6a3ea62787254a0b329397df37986afcd1a1bcb0202e4c51c545fa56c'
progress = HERE / 'current-progress.md'
assert (HERE / 'proof-commit.txt').read_text().strip() == 'f4ee8978f3a907da7cbd926998a0a2fd0475b85f'
assert load(HERE / 'verification.json')['status'] == 'PASS'
assert not (HERE / 'completed-root-support').exists()
before, addition = progress.read_bytes(), proposal.read_bytes()
assert addition.startswith(b'\n## Checked cluster admission and closing state\n')
assert b'## Checked cluster admission and closing state' not in before
progress.write_bytes(before + addition)
assert progress.read_bytes()[:-len(addition)] == before
print('Appended actual checked closing state; seal and push remain future.')
