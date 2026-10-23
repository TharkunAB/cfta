exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-cluster-admission-history-revision-v2')
checked_package(owner, '1815d15348ee7f7dcaef662ead7983a98a2b923f0cf47dcbb9922891491a1fae', 'a74457c366c5235249539ba17630a054446aa8271a8b9fd915bb45d02f6dba10')
audit = Path('/tmp/mcfta-cluster-admission-history-revision-audit')
checked_package(audit, '906e2b6e624b79589dc17312b4ef50788f5b41fa82f0011fa7e3bd235dc4243a', '17339a2ed8f26d8b2a500bc24872f41ff648ef4f46770e66787264dca3254c7a')
assert sha(audit / 'review.json') == 'cd8f80013be7e6dd159d33537137877f0e515364e74ec35b990f91524c99dc99'
active = HERE / 'source-history-gate.json'
assert active.read_bytes() == (owner / 'source-history-v1.json').read_bytes()
before, after = load(active), load(owner / 'source-history-v2.json')
variants = {item['path'] for item in before['variants']}
assert len(variants) == 6 and len(before['artifacts']) == 591
assert [item for item in before['artifacts'] if item['path'] not in variants] == after['artifacts']
assert len(after['artifacts']) == 585
assert {k:v for k,v in before.items() if k != 'artifacts'} == {k:v for k,v in after.items() if k != 'artifacts'}
assert not variants & {item['path'] for item in after['artifacts']}
archive(owner, 'source-history-revision-v2')
archive(audit, 'source-history-revision-audit')
save('root-source-history-revision-review.json', dict(
    status='ACCEPTED_EXACT_METADATA_REVISION_BEFORE_VERIFIER_V2',
    original_history_sha256=sha(active), revised_history_sha256=sha(owner / 'source-history-v2.json'),
    independent_review_sha256=sha(audit / 'review.json'),
    original_root_review_sha256=sha(HERE / 'root-source-history-review.json'),
    removed_only_six_duplicate_artifact_records=True, all_six_variants_unchanged=True,
    remaining_artifacts_unchanged=585, mathematical_sources_unchanged=True,
    all_jobs_and_failures_unchanged=True, old_history_and_reviews_retained=True))
active.write_bytes((owner / 'source-history-v2.json').read_bytes())
assert sha(active) == '850aaf693105d499717232fb676597b3a7202e65424dfaa6caa6f0d1bd333bc1'
print('ACCEPTED and activated exact reviewed metadata revision; mathematical sources and jobs unchanged.')
