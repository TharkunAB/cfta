exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
assessment = Path('/tmp/mcfta-generated-inventory-route-assessment')
checked_package(assessment, 'a9cfdf0a49247faea263e355223eba0fd9fbe8ea213b2ca496c3fe41c4fec9a4', '431acb81512171c8eac01d1f9dafd2c43054ed87816a3262cdeb7614ea927bbe')
assert (HERE / 'proof-commit.txt').read_text().strip() == '65b08c2c8f539390761f3d43805e8c0cc6e3d94d'
for mode in ['normal', 'live']:
    assert load(HERE / ('proof-evidence-' + mode + '.json'))['status'] == 'PASS'
archive(assessment, 'next-route-assessment')
progress = HERE / 'current-progress.md'
addition = Path('/tmp/mcfta-rebuild-admission-progress-final.md').read_bytes()
assert addition not in progress.read_bytes()
with progress.open('ab') as output:
    output.write(addition)
print('Recorded actual proof results, historical cuts, later metadata failures and the unproved next route.')
