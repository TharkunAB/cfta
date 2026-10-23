exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import sys

expected_pins, expected_freeze, expected_review = sys.argv[1:]
peer = Path('/tmp/mcfta-demand-node-counter-growth-source-history-audit')
checked_package(peer, expected_pins, expected_freeze)
assert sha(peer / 'review.json') == expected_review
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and review['scope'] == 'INDEPENDENT_COMPLETE_INSTALLED_SOURCE_AND_ACTUAL_HISTORY_CUT_REVIEW'
assert review['module'] == NAME and review['source_sha256'] == 'c94db7eee4e7aa54d00f30ed4703301e5b4b5cefb106c1c619cc95994d3676f0'
assert review['actual_proof_cut_sha256'] == sha(HERE / 'actual-proof-cut.json') == 'fff629d054d2e606437506be9f7ba2d6ea1cf53e30428e1d583d58e0ed90926d'
assert review['source_history_sha256'] == sha(HERE / 'source-history-gate.json') == 'e5fce2a41a2e3eed307fd38fea089f2f271e6730edc99bb87779f37d655120b5'
cut = load(HERE / 'actual-proof-cut.json')
history = load(HERE / 'source-history-gate.json')
assert cut['metrics'] == dict(actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1, failed_jobs=0, warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0)
assert cut['variants'] == len(history['variants']) == 1 and cut['patches'] == len(history['patches']) == 0
assert not history['rejected_public_types'] and cut['artifacts'] == len(history['artifacts']) == 763
assert cut['metadata_jobs'] == 13 and cut['failed_metadata_jobs'] == 0
for item in history['artifacts']:
    path = HERE / item['path']
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], path
for item in history['variants']:
    path = HERE / item['path']
    assert sha(path) == item['sha256'] and len(path.read_bytes().splitlines()) == item['lines'] == 80
    assert path.read_bytes() == (ROOT / ('lean/MicroCFTA/' + NAME + '.lean')).read_bytes() == (HERE / (NAME + '.lean')).read_bytes()
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == ('import MicroCFTA.' + NAME + '\n').encode() + (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert cut['audit']['build_jobs'] == 3655 and cut['audit']['dependencies'] == 75560
assert cut['audit']['log_sha256'] == sha(HERE / 'audit1.log') == '255bbf2ca92db811b215e1f915882870c64f3da513c1795c777675aa8e45b541'
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for stem in ['strict1', 'FULL1', 'audit1']:
    receipt = load(HERE / (stem + '.json'))
    assert receipt['exit_code'] == 0 and load(HERE / receipt['limits']) == limits
    usage = load(HERE / (stem + '.usage.json'))
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
    assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
for name in load(HERE / 'root-metadata-history-cut.json')['jobs']:
    receipt = load(HERE / name)
    stem = Path(name).stem
    assert receipt['exit_code'] == 0
    assert load(HERE / ('root-metadata-history/' + stem + '.limits.json')) == limits
    usage = load(HERE / ('root-metadata-history/' + stem + '.usage.json'))
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
assert (HERE / 'strict1.log').read_bytes() == b''
assert load(HERE / 'root-full-review.json')['root_manual_complete_TYPEs']
archive(peer, 'source-history-audit')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    module=NAME, source_sha256=review['source_sha256'], source_lines=80,
    root_whole_installed_source_and_single_variant_read=True,
    root_whole_collector_and_common_read=True,
    root_all_actual_receipts_caps_usage_and_history_pins_checked=True,
    independent_review_sha256=expected_review, actual_proof_cut_sha256=sha(HERE / 'actual-proof-cut.json'),
    source_history_sha256=sha(HERE / 'source-history-gate.json'), actual_metrics=cut['metrics'], actual_Audit=cut['audit'],
    canonical_copy_created_by_reviewed_materializer=True, complete_public_TYPEs_reviewed=True,
    BODY_programmatic_only=True, H6_remains_strongest_combined=True,
    no_Haskell_repair_required=True, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the complete installed source and actual history. Historical cuts stay immutable; later support remains separate.')
