exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
peer = Path('/tmp/mcfta-native-node-counter-growth-source-history-audit')
checked_package(peer, 'f40cae521e0f7ef853546587cdd71cd5d018013f860d905bab29c13f9fe93b48', '6faf8ded31a043a133dfba26e9710e7b0803cdb2899739284a8ead1806e43294')
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_math_author']
cut = load(HERE / 'actual-proof-cut.json')
assert sha(HERE / 'actual-proof-cut.json') == '733fcfe8c4618b9904b2e08947c32c3ecf7e2406ea02fa223d2ab8133c804dd3'
assert sha(HERE / 'source-history-gate.json') == '837548791edbab605630e73db035f5fc9f9e79bae610ab3468be4d13090d87fb'
assert cut['metadata_jobs'] == 13 and cut['failed_metadata_jobs'] == 0
assert [cut[key] for key in ['variants', 'patches', 'artifacts']] == [1, 0, 692]
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == 'b43e0c75517bb57db8a062d45c2282c9117ce3944d5086d323318790a8fb9bec'
history = load(HERE / 'source-history-gate.json')
for pin in history['variants'] + history['artifacts']:
    path = HERE / pin['path']
    assert sha(path) == pin['sha256']
    if 'bytes' in pin:
        assert path.stat().st_size == pin['bytes']
archive(peer, 'source-history-audit')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    module=NAME, source_sha256=sha(HERE / (NAME + '.lean')), source_lines=79,
    root_whole_installed_source_and_single_variant_read=True, root_whole_collector_and_common_read=True,
    root_all_actual_receipts_caps_usage_and_history_pins_checked=True,
    independent_review_sha256=sha(peer / 'review.json'),
    actual_proof_cut_sha256=sha(HERE / 'actual-proof-cut.json'), source_history_sha256=sha(HERE / 'source-history-gate.json'),
    actual_metrics=cut['metrics'], actual_Audit=cut['audit'], canonical_copy_created_by_reviewed_materializer=True,
    complete_public_TYPEs_reviewed=True, BODY_programmatic_only=True,
    H6_remains_strongest_combined=True, no_Haskell_repair_required=True, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the complete installed source and actual retained proof history.')
