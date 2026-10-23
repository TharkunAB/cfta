import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

package = Path('/tmp/mcfta-comparison-native-covered-early-tools')
entries = checked_package(package,
    '2ee39763258bc0c5163b288a7a9dc901202aea46852fbb0a1b6fe81d0eccc9e6',
    'd4e058a7d270818a7e6e21e851fbcc14d1b45a478a571313d594bc04ef9856ad')
audit = Path('/tmp/mcfta-comparison-native-covered-early-tools-audit')
checked_package(audit,
    '89f0bc7b6fd8b8f75a7a11ee578c440d768fbd52284ce8e886c0299a5c7feddb',
    '2f29a1fdfd612678886dd94defef7e092233e5e371a2cf6a6f632c7afbcd5103')
assert sha(audit / 'review.json') == '02e0a8f5309d0ef1623c019d57279cc6d83a2eccd7689b044427714d63827b0f'
review = load(audit / 'review.json')
assert review['status'] == 'SOURCE_ONLY_CLEAR' and not review['cap_accepted']
assert review['lines'] == 210 and review['unchanged_AST_assertions'] == 53
assert review['prepared_tools_executed'] == 0
assert len(entries) == 12
expected = {
    'root-run-check.py': '37784c72c779cac7e5cbd2bfdbfaf10bf90a1cda37c117debe04495b74d604ff',
    'check-full-public.py': '4307c7947f078155fd815e9439fc5d017e92a43aec1ada67e514ce2b8c3a38f1',
    'prepare-selected-full.py': 'bcd830849b493c77eb6327c73d1d1d4d083dd0503a644ff529cc068ae326081b',
}
archive(package, 'early-tools')
archive(audit, 'early-tools-audit')
for name, digest in expected.items():
    source = package / 'selected' / name
    assert sha(source) == digest and not (HERE / name).exists()
    (HERE / name).write_bytes(source.read_bytes())
(HERE / 'full-preparation').mkdir()
(HERE / 'full-preparation/diagnostic-tail.lean.txt').write_bytes((package / 'diagnostic-tail.lean.txt').read_bytes())
save('root-early-tools-review.json', dict(status='ROOT_SOURCE_ONLY_ACCEPTED',
    root_whole_selected_sources_read=3, lines=210, unchanged_assertions=53,
    tools=expected, independent_review_sha256=sha(audit / 'review.json'),
    proposed_source_cap=230, cap_accepted=False, proof_jobs=0,
    compiler_activation_requires='Accepted exact declarations/cap and independent full body review',
    whole_goal_complete=False))
print(json.dumps(dict(status='PASS', installed_tools=3, proof_jobs=0, cap_accepted=False)))
