exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
audit = Path('/tmp/mcfta-rebuild-admission-source-history-audit')
checked_package(audit, '90e1fa22b5469a631fb51a64ddc478e66d77f2b091b9b257dc06873f15a53bfd', '9720963644a23b482f944575c54cba33c2a824c578a0242b11c1cf078f176e75')
assert sha(audit / 'review.json') == 'cb67feb3cb57a9e6890f1092c36642bd677c5666a745f260a139abdfda9af111'
assert load(audit / 'review.json')['status'] == 'CLEAR'
history = HERE / 'source-history-gate.json'
assert sha(history) == '807e517fab30722712c3a65cf517d5fc6520960a5f80ee6f35736f7568694277'
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == '355224ff767c10856684db24c0d6393e61c63a6754ae6044bb64ba29b0ca61e7'
cut = load(HERE / 'actual-proof-cut.json')
assert cut['metrics']['actual_jobs'] == 3 and cut['artifacts'] == 467
assert cut['metadata_jobs'] == 13 and cut['failed_metadata_jobs'] == 0
archive(audit, 'source-history-audit')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    root_whole_selected_source_lines_read=90, root_all_complete_public_TYPEs_read=True,
    source_history_sha256=sha(history), independent_review_sha256=sha(audit / 'review.json'),
    actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1, failed_source_jobs=0,
    variants=1, artifacts=467, root_metadata_cut_jobs=13, failed_root_metadata_jobs=0,
    Audit_one_import_inverse=True, new_theorem_result_claimed=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED whole selected source and independently checked actual history.')
