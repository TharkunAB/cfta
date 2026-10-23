import runpy
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

stem = 'pair-request-admission-strict-1'
source = HERE / (stem + '.source.lean')
assert load(HERE / (stem + '.json'))['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
assert sha(source) == '103064aca3b5320b00e001823e6fd372ff51f1768b6dbf8683a8ed58148e5cfe'
assert len(source.read_bytes().splitlines()) == 157
report = dict(status='ROOT_ACCEPTED_CLEAN_STRICT_FOR_FULL', source_sha256=sha(source),
    source_lines=157, selected_strict=stem, strict_log_literal_empty=True,
    actual_jobs=1, failed_jobs=0, full_jobs=0, official_install_authorized=False)
save('root-source-review.json', report)
subprocess.run(['/usr/bin/python3', str(HERE / 'prepare-selected-full.py'), stem, sha(source), '157',
    '33534ddc06a88f5cfdb870d21ad2985beab47f5f6ed27e83bf5a78418bc37383', '9',
    'eb2c599427677c60b1cf3c2cd68e37b5debf79b08a1588a36853db0905ecd757', '24'], check=True)
print(json.dumps(report))
