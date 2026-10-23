exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
peer = Path('/tmp/mcfta-stored-node-counter-growth-source-history-audit')
checked_package(peer, expected_pins, expected_freeze)
assert sha(peer / 'review.json') == expected_review
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_math_author']
cut = load(HERE / 'actual-proof-cut.json')
assert sha(HERE / 'actual-proof-cut.json') == 'fd2fccafd0aa18f7aa1aee7695ac69c8bbc8643e6b40206413354a9c25df6531'
assert sha(HERE / 'source-history-gate.json') == '124b9bed8354602aa8e01a18373234324511f6c410c723aa460adef1347479e6'
assert cut['metadata_jobs'] == 13 and cut['failed_metadata_jobs'] == 0
assert [cut[k] for k in ['variants', 'patches', 'artifacts']] == [1, 0, 856]
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == '2dc66e6e7cc728b051a65d622f6aab9bd236ac485b90eb4c1f60650fc438d16a'
archive(peer, 'source-history-audit')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    module=NAME, source_sha256=sha(HERE / (NAME + '.lean')), source_lines=82,
    root_whole_installed_source_and_single_variant_read=True, root_whole_collector_and_common_read=True,
    root_all_actual_receipts_caps_usage_and_history_pins_checked=True, independent_review_sha256=expected_review,
    actual_proof_cut_sha256=sha(HERE / 'actual-proof-cut.json'), source_history_sha256=sha(HERE / 'source-history-gate.json'),
    actual_metrics=cut['metrics'], actual_Audit=cut['audit'], early_canonical_copy_retained=True,
    complete_public_TYPEs_reviewed=True, BODY_programmatic_only=True,
    H6_remains_strongest_combined=True, no_Haskell_repair_required=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED complete installed source and actual retained history.')
