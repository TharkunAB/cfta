import runpy
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

stem = 'completed-hit-readback-strict-1'
source = HERE / (stem + '.source.lean')
assert load(HERE / (stem + '.json'))['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
assert sha(source) == '4bf1df4098cbc276613106c45d1279a1ce156bb3832b6c813874a3c568522c15'
assert len(source.read_bytes().splitlines()) == 147
report = dict(status='ROOT_ACCEPTED_CLEAN_STRICT_FOR_FULL', source_sha256=sha(source),
    source_lines=147, selected_strict=stem, strict_log_literal_empty=True,
    actual_jobs=1, failed_jobs=0, full_jobs=0, official_install_authorized=False)
save('root-source-review.json', report)
subprocess.run(['/usr/bin/python3', str(HERE / 'prepare-selected-full.py'), stem, sha(source), '147',
    'b673b23605415389111a2755228c368bbdda8ffd96e7fb10ab729549a3bb425f', '11',
    'fcddd53d1bd7d54c3f571049a3cbdca3365c367f172bce02cbef87d9817d2d89', '12'], check=True)
print(json.dumps(report))
