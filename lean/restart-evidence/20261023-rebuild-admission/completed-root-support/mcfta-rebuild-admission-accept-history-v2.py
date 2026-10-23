exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
audit = Path('/tmp/mcfta-rebuild-admission-source-history-audit-v2')
checked_package(audit, 'de9a48e84286a9228705926bef23f5b9c493ce7beb470b4ed12e7bd25a7751d6', 'a9798f661163a91ee6c5edd133cf15485ce54164f6bc08df5fe55a20f42d054c')
assert sha(audit / 'review.json') == 'cb67feb3cb57a9e6890f1092c36642bd677c5666a745f260a139abdfda9af111'
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert sha(audit / 'coverage-correction.json') == '4a7ad67b3f04140a86b264cea0539391083f57e012fc81dd37012c23e639915b'
original = Path('/tmp/mcfta-rebuild-admission-source-history-audit')
for item in original.rglob('*'):
    if item.is_file():
        relative = item.relative_to(original)
        retained = audit / ('historical-v1-controls' if len(relative.parts) == 1 and relative.name in {'pins.json', 'FROZEN.json'} else '') / relative
        assert item.read_bytes() == retained.read_bytes(), relative
history = HERE / 'source-history-gate.json'
assert sha(history) == '807e517fab30722712c3a65cf517d5fc6520960a5f80ee6f35736f7568694277'
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == '355224ff767c10856684db24c0d6393e61c63a6754ae6044bb64ba29b0ca61e7'
cut = load(HERE / 'actual-proof-cut.json')
assert cut['metrics']['actual_jobs'] == 3 and cut['artifacts'] == 467
assert cut['metadata_jobs'] == 13 and cut['failed_metadata_jobs'] == 0
assert load(audit / 'closing-metadata-failure/mcfta-rebuild-admission-history-acceptance-1.json')['exit_code'] != 0
archive(audit, 'source-history-audit-v2')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    root_whole_selected_source_lines_read=90, root_all_complete_public_TYPEs_read=True,
    source_history_sha256=sha(history), independent_review_sha256=sha(audit / 'review.json'),
    actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1, failed_source_jobs=0,
    variants=1, artifacts=467, root_metadata_cut_jobs=13, failed_root_metadata_jobs=0,
    closing_metadata_failed_attempts_outside_historical_cut=1,
    package_coverage_correction_sha256=sha(audit / 'coverage-correction.json'),
    original_v1_bytes_preserved=True, nested_control_now_pinned=True,
    Audit_one_import_inverse=True, new_theorem_result_claimed=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED whole selected source and actual history; complete V2 coverage, V1 and failed metadata attempt retained.')
