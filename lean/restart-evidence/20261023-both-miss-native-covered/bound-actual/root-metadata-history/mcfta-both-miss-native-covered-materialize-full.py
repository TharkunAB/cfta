import runpy
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

stem = 'both-miss-native-covered-strict-1'
source = HERE / (stem + '.source.lean')
assert load(HERE / (stem + '.json'))['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
assert sha(source) == '09e8927b6e9a98fa39704567fd6b48164dfc2a30d45ea389e0d8e4a36d71116b'
assert len(source.read_bytes().splitlines()) == 152
report = dict(status='ROOT_ACCEPTED_CLEAN_STRICT_FOR_FULL', source_sha256=sha(source),
    source_lines=152, selected_strict=stem, strict_log_literal_empty=True,
    actual_jobs=1, failed_jobs=0, full_jobs=0, official_install_authorized=False)
save('root-source-review.json', report)
subprocess.run(['/usr/bin/python3', str(HERE / 'prepare-selected-full.py'), stem, sha(source), '152',
    '1c6016075403d073fca56a0667c0f41c4e4f1f4e1c38739f292dd74cda9279bd', '21',
    '41ba0c705d0ff6a6de29d07d5c4ffbc8da50bef810851aef9f92300eb9e27c90', '67'], check=True)
print(json.dumps(report))
