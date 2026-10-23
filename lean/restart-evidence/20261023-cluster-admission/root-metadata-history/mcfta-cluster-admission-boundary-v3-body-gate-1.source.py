exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-cluster-admission-boundary-source-v3')
review = Path('/tmp/mcfta-cluster-admission-boundary-body-v3-audit')
checked_package(owner, '3dfb9d663761953b29a726f633eb8387870830ec17ca9505924b4eae70885238', '10ed0421cd7c8d64ae891308b1d8e77109ef157fca76abda82c0ab690fdf0ae4')
checked_package(review, 'a42398b0f0902fe0f8484f0f54ca1e339883f05bcabd362bd29031e352ae9164', '36e347a08f1fac4a820dace4cace0961bd18920dd0bc213c6466522132e7e2e2')
assert load(review / 'review.json')['status'] == 'CLEAR'
source = owner / 'SourceCurrentOriginalRowClusterAdmissionBoundary.lean'
assert sha(source) == 'd610d762a429313d324e6184265d793312a2e8ac05d24c936dc350a4b5be8b93'
assert len(source.read_text().splitlines()) == 199
before = (HERE / 'boundary-source-v2/SourceCurrentOriginalRowClusterAdmissionBoundary.lean').read_text()
first = (HERE / 'boundary-declaration-v2/context.lean.txt').read_text().rstrip('\n')
second = (HERE / 'boundary-declaration-v3/context.lean.txt').read_text().rstrip('\n')
assert source.read_text() == before.replace(first, second)
assert load(HERE / 'root-boundary-declaration-v3-gate.json')['body_authoring_authorized']
assert load(HERE / 'boundary-strict2.json')['exit_code'] == 1
archive(owner, 'boundary-source-v3')
archive(review, 'boundary-body-v3-audit')
save('root-boundary-v3-body-gate.json', {
    'status': 'ACCEPTED_SOURCE_BODY_FOR_STRICT', 'source_sha256': sha(source), 'source_lines': 199,
    'root_complete_source_and_exact_context_delta_read': True,
    'independent_body_review_sha256': sha(review / 'review.json'),
    'declaration_gate': 'root-boundary-declaration-v3-gate.json', 'whole_source_hard_stop': 230,
    'strict_compiler_activation_authorized': True, 'FULL_activation_authorized': False,
    'default_declaration_limits': True, 'all_linters': True,
    'v1_v2_failed_strict_history_retained': True, 'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: complete199-line V3 boundary accepted for strict3')
