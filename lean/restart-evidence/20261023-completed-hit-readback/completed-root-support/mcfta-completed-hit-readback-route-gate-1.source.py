import datetime
import runpy
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

previous = ROOT / 'lean/restart-evidence/20261023-both-miss-native-covered'
source = previous / 'next-comparison-inventory'
audit = previous / 'next-comparison-audit'
checked_package(source, '7c26f01b2f5d8d9d96dddc726c265d324ba977a9d993a83641ff9c8f745de451',
    'a3ec5609bdc1936b03cfb815c17a6a82c45b3bb94d7160038cf697d8500f8818')
checked_package(audit, 'dd131ed99bb6f98e9dcd1ea39ac2924c55fd6d7bd8137d2cbbc3c6f0942412dc',
    '6c2e55baad6bdbdd6bcd0b68ba70c3f220443f59762a85677d855804ecd93899')
assert sha(audit / 'review.json') == 'c9fa4df1dae00c515731349a8fff1702a93b1d0fa22de9b71b847d532266a0c2'
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert load(previous / 'root-next-comparison-review.json')['status'] == 'SOURCE_ONLY_ROUTE_CLEAR'
assert load(HERE / 'previous-authorized-push.json')['checkpoint'] == START
assert git('rev-parse', 'HEAD').strip() == START
index = load(source / 'source-index.json')
assert len(index['sources']) == 28
cuts = lines = 0
for item in index['sources']:
    path = ROOT / item['path']
    data = path.read_bytes()
    assert data == (source / item['snapshot']).read_bytes()
    assert sha(path) == item['sha256'] and len(data) == item['bytes']
    assert len(data.splitlines()) == item['lines']
    for cut in item['cuts']:
        retained = source / cut['snapshot']
        assert retained.read_bytes() == b''.join(data.splitlines(True)[cut['start']-1:cut['end']])
        assert sha(retained) == cut['sha256'] and retained.stat().st_size == cut['bytes']
        cuts += 1
        lines += cut['end'] - cut['start'] + 1
assert cuts == 38 and lines == 1058
save('root-route-review.json', dict(status='ROOT_CURRENT_SOURCE_ROUTE_CLEAR',
    observed_at=datetime.datetime.now().astimezone().isoformat(),
    previous_turn='PROGRESS: verified H26 theorem and evidence pushed',
    source_inventory=str(source.relative_to(ROOT)), source_inventory_pins_sha256=sha(source / 'pins.json'),
    independent_review=str((audit / 'review.json').relative_to(ROOT)),
    independent_review_sha256=sha(audit / 'review.json'),
    current_live_sources=28, exact_cuts=38, cut_lines=1058,
    root_read_scope='Complete note, plain contract, route/budgets/provenance and all1058 selected cut lines read in the preceding turn. Every source identity and cut revalidated against the current pushed baseline.',
    module='MicroCFTA.' + NAME, proposed_source_estimate=[110,160], source_hard_stop=180,
    public_goal='after.checked = before.checked for the SAME supplied completed-hit H7 run',
    genuine_premises='Initial Stable, actual published original/reverse key and actual supplied done equation',
    proposed_private_obligations=['yielded-prefix completion inversion', 'ret-control checked-state preservation'],
    exact_signature_proposal_authorized=True, proof_body_authorized=False,
    compiler_or_prepared_tool_authorized=False, whole_goal_complete=False))
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Current source route gate\n\nAll 28 source identities and 38 cuts match the reviewed pushed baseline.\nRoot and independent source-only route reviews remain valid.\nAn exact declaration proposal is authorized with a 180-line whole-source stop.\nIt must retain the SAME supplied done equation and full returned state.\nNo body, compiler or prepared tool is authorized by this gate.\n')
print(json.dumps(dict(status='PASS', current_sources=28, cuts=38, cut_lines=1058,
    exact_signature_proposal_authorized=True, whole_goal_complete=False)))
