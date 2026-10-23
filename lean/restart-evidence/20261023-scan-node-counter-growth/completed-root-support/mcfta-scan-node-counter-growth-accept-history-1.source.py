exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import hashlib
import sys

peer = Path('/tmp/mcfta-scan-node-counter-growth-source-history-review')
checked_package(peer, sys.argv[1], sys.argv[2])
assert sha(peer / 'review.json') == sys.argv[3]
assert load(peer / 'review.json')['status'] == 'CLEAR'
history = load(HERE / 'source-history-gate.json')
cut = load(HERE / 'actual-proof-cut.json')
jobs = load(HERE / 'job-history.json')
metadata = load(HERE / 'root-metadata-history-cut.json')
assert sha(HERE / 'source-history-gate.json') == cut['source_history_sha256'] == '70c275499b83c169977d69d0c9996652736f24605195f1efc7fd150978c2b678'
assert history['status'] == 'ROOT_ACCEPTED' and history['patches'] == history['rejected_public_types'] == []
assert (len(history['variants']), len(history['artifacts'])) == (cut['variants'],cut['artifacts']) == (1,924)
paths = set()
for record in history['variants'] + history['artifacts']:
    path = HERE / record['path']
    assert record['path'] not in paths
    paths.add(record['path'])
    assert sha(path) == record['sha256']
    if 'bytes' in record:
        assert path.stat().st_size == record['bytes']
    else:
        assert len(path.read_bytes().splitlines()) == record['lines'] == 80
assert set(jobs) == {'root-scan-node-counter-growth-strict-1','root-scan-node-counter-growth-full-1','root-scan-node-counter-growth-audit-1'}
assert cut['metrics'] == dict(actual_jobs=3,source_jobs=2,focused_build_jobs=0,audit_jobs=1,failed_jobs=0,warned_source_exit_zero_jobs=0,rejected_public_type_jobs=0)
assert all(item['exit_code'] == item['errors'] == item['source_warnings'] == 0 for item in jobs.values())
assert len(metadata['jobs']) == cut['metadata_jobs'] == 21
failed = [name for name, code in metadata['jobs'].items() if code]
assert failed == cut['metadata_failure_paths'] == ['root-metadata-history/mcfta-scan-node-counter-growth-accept-next-consumer-investigation-1.json']
assert metadata['failed_jobs'] == cut['failed_metadata_jobs'] == 1
for name, code in metadata['jobs'].items():
    assert load(HERE / name)['exit_code'] == code
    for suffix in ['.json','.log','.limits.json','.usage.json','.source.py','.peaks.txt']:
        relative = name[:-5] + suffix
        assert relative in paths
        assert (HERE / relative).read_bytes() == (Path('/tmp') / Path(relative).name).read_bytes()
archive(peer, 'source-history-audit')
save('root-source-history-review.json', {
    'status':'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY', 'module':NAME,
    'source_sha256':sha(HERE / (NAME + '.lean')), 'source_lines':80,
    'root_complete_selected_source_and_all_declarations_reviewed':True,
    'all_925_variant_artifact_hashes_and_sizes_or_lines_checked':True,
    'source_history_sha256':sha(HERE / 'source-history-gate.json'),
    'job_history_sha256':sha(HERE / 'job-history.json'),
    'actual_proof_cut_sha256':sha(HERE / 'actual-proof-cut.json'),
    'metadata_cut_sha256':sha(HERE / 'root-metadata-history-cut.json'),
    'metrics':cut['metrics'], 'variants':1,'patches':0,'artifacts':924,
    'metadata_jobs':21,'failed_metadata_jobs':1,
    'metadata_reader_failure_and_corrected_retry_retained_and_not_Lean_failures':True,
    'independent_review_sha256':sha(peer / 'review.json'),
    'default_declaration_limits':True,'all_linters':True,
    'no_new_Lean_or_Lake_jobs':True,'goal_status':'ACTIVE_INCOMPLETE'})
print('PASS: all925 actual variant/artifact identities and all21 metadata bundles accepted.')
