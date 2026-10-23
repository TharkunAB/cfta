exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import sys

peer = Path(sys.argv[1])
checked_package(peer,sys.argv[2],sys.argv[3])
assert load(peer / 'review.json')['status'] == 'CLEAR'
history = load(HERE / 'source-history-gate.json')
cut = load(HERE / 'actual-proof-cut.json')
jobs = load(HERE / 'job-history.json')
metadata = load(HERE / 'root-metadata-history-cut.json')
assert history['status'] == 'ROOT_ACCEPTED'
assert len(history['variants']) == cut['variants'] == 1
assert len(history['artifacts']) == cut['artifacts'] == 1176
assert history['patches'] == history['rejected_public_types'] == []
assert cut['patches'] == 0
variants = {item['path']:item for item in history['variants']}
artifacts = {item['path']:item for item in history['artifacts']}
assert not set(variants) & set(artifacts)
assert len(variants) == 1 and len(artifacts) == 1176
for path,pin in {**variants,**artifacts}.items():
    item = HERE / path
    assert sha(item) == pin['sha256'],path
    if path in artifacts:
        assert item.stat().st_size == pin['bytes'],path
    else:
        assert len(item.read_bytes().splitlines()) == pin['lines'] == 96
        assert item.read_bytes() == (HERE / (NAME + '.lean')).read_bytes()
assert cut['source_history_sha256'] == sha(HERE / 'source-history-gate.json')
assert cut['metrics'] == dict(actual_jobs=3,source_jobs=2,focused_build_jobs=0,audit_jobs=1,failed_jobs=0,warned_source_exit_zero_jobs=0,rejected_public_type_jobs=0)
assert len(jobs) == 3
for stem,job in jobs.items():
    receipt = load(HERE / (stem + '.json'))
    assert receipt['exit_code'] == job['exit_code'] == job['errors'] == job['source_warnings'] == 0
    assert sha(HERE / receipt['log']) == job['log_sha256']
    assert load(HERE / receipt['limits']) == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
    usage = load(HERE / (stem + '.usage.json'))
    assert usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
assert len(metadata['jobs']) == cut['metadata_jobs'] == 18
assert metadata['failed_jobs'] == cut['failed_metadata_jobs'] == 0
assert cut['metadata_failure_paths'] == [] and all(code == 0 for code in metadata['jobs'].values())
for path,code in metadata['jobs'].items():
    assert load(HERE / path)['exit_code'] == code
    for suffix in ['.json','.log','.limits.json','.usage.json','.source.py','.peaks.txt']:
        assert path[:-5] + suffix in artifacts
assert cut['audit']['build_jobs'] == 3656 and cut['audit']['dependencies'] == 75572
assert cut['audit']['log_sha256'] == load(HERE / 'root-cohort-audit-gate.json')['log_sha256']
assert sha(HERE / 'root-pair-node-counter-growth-strict-1.source.lean') == '6cfaf5e340d26b8c838f51d93fb3ae0e03b098510ca41b5021ada4e96b72c2e8'
assert (HERE / 'root-pair-node-counter-growth-strict-1.log').read_bytes() == b''
archive(peer,'source-history-audit')
save('root-source-history-review.json',dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    module=NAME,source_sha256='6cfaf5e340d26b8c838f51d93fb3ae0e03b098510ca41b5021ada4e96b72c2e8',source_lines=96,
    root_complete_selected_source_and_all_declarations_reviewed=True,
    all_1177_variant_artifact_hashes_and_sizes_or_lines_checked=True,
    source_history_sha256=sha(HERE / 'source-history-gate.json'),
    job_history_sha256=sha(HERE / 'job-history.json'),actual_proof_cut_sha256=sha(HERE / 'actual-proof-cut.json'),
    metadata_cut_sha256=sha(HERE / 'root-metadata-history-cut.json'),
    metrics=cut['metrics'],variants=1,patches=0,artifacts=1176,metadata_jobs=18,failed_metadata_jobs=0,
    metadata_corrections_retained_and_not_Lean_failures=True,
    independent_review_sha256=sha(peer / 'review.json'),default_declaration_limits=True,all_linters=True,
    no_new_Lean_or_Lake_jobs=True,goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the complete actual source history, all artifact identities and all separate metadata attempts.')
