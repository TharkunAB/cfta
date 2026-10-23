exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
audit = Path('/tmp/mcfta-group-admission-source-history-audit')
checked_package(audit, '560dedfb36cb7b122481a185bb7d44aad5b0128d43a7c2bb732332a5b2b2c611', '85d828450b37138a788427545e24b9d46e44141add0bb80360765e2a717f57e2')
review = load(audit / 'review.json')
assert sha(audit / 'review.json') == '6a643f6e911060f2f2c1fc3c0f8009e5f8e5ea48c831ccf1eb5440245ac5b129'
assert review['status'] == 'CLEAR' and review['whole_100_line_source_read']
assert review['proof_jobs'] == 3 and review['artifacts_hashed'] == 506
assert review['metadata_jobs'] == 12 and review['failed_metadata_jobs'] == 0
assert review['variant_artifact_paths_disjoint'] and review['alias_rename_exact']
history = HERE / 'source-history-gate.json'
assert sha(history) == '8b5735afadbdbc97741b30dae64d1f3155329ad454e6dcf5fc24cd14ed50f8f0'
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == review['source_sha256']
assert load(HERE / 'actual-proof-cut.json')['metrics']['actual_jobs'] == 3
archive(audit, 'source-history-audit')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    root_whole_selected_source_lines_read=100, root_all_complete_public_TYPEs_read=True,
    source_history_sha256=sha(history), independent_review_sha256=sha(audit / 'review.json'),
    actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1, failed_source_jobs=0,
    variants=1, artifacts=506, root_metadata_cut_jobs=12, failed_root_metadata_jobs=0,
    source_alias_exact=True, Audit_one_import_inverse=True,
    new_theorem_result_claimed=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED whole selected source and independently checked actual history.')
