exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
audit = Path('/tmp/mcfta-pair-inventory-rebase-source-history-audit')
checked_package(audit, 'bf1b435f74926c052b671006743d6ec6c8499543e676b24fb9bb8cb02c6146a3', 'c94d9f26fda0e9deceb58c84bee93217e86237f209bc72c6efed986cec12f83d')
assert sha(audit / 'review.json') == '46cf34074a0296e2586139ee5401d57980ba1dad98c323ab671cd656fdf575a1'
assert load(audit / 'review.json')['status'] == 'CLEAR'
history = HERE / 'source-history-gate.json'
assert sha(history) == '8fa22a9f18d4a3b7869fd39c6ddadfb2b8771c948a4d8e7e0ce4b4512d35a460'
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == 'b7351e92c6981f5caa5d7a18a05676912b9ee741c94cc2a39f1ba3ef74b03840'
cut = load(HERE / 'actual-proof-cut.json')
assert cut['metrics']['actual_jobs'] == 3 and cut['artifacts'] == 504
assert cut['metadata_jobs'] == 14 and cut['failed_metadata_jobs'] == 0
assert cut['audit']['build_jobs'] == 3651 and cut['audit']['dependencies'] == 75528
archive(audit, 'source-history-audit')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    root_whole_selected_source_lines_read=77, root_all_complete_public_TYPEs_read=True,
    source_history_sha256=sha(history), independent_review_sha256=sha(audit / 'review.json'),
    actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1, failed_source_jobs=0,
    variants=1, artifacts=504, root_metadata_cut_jobs=14, failed_root_metadata_jobs=0,
    complete_nested_control_coverage=True, Audit_one_import_inverse=True,
    new_theorem_result_claimed=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED complete selected source and actual source/history cut; no repair or failed compiler job.')
