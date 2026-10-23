exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-original-row-cluster-admission-signature-v3')
review = Path('/tmp/mcfta-cluster-admission-outer-declaration-v3-audit')
checked_package(owner, '66cd53e87a72f069053cbe6edc882859ec9f3ae95bb4479ce2c1df3b8c3a481b', '0fe58a7aef6a62158dd846fce3b6e90312f943ed55502b445102333e6d527f3e')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
contracts = load(owner / 'contracts.json')
assert len(contracts) == 11
for name, digest in contracts.items():
    assert sha(owner / name) == digest
for item in load(owner / 'source-index.json')['sources']:
    assert sha(ROOT / item['path']) == item['sha256']
schema = load(owner / 'declaration-schema.json')
assert schema['private_helpers'] == [] and schema['global_definitions'] == []
assert len(schema['local_have_names']) == 4 and schema['local_let_names'] == []
archive(Path('/tmp/mcfta-original-row-cluster-admission-signature'), 'outer-declaration-plan-v1')
archive(Path('/tmp/mcfta-original-row-cluster-admission-signature-v2'), 'outer-declaration-plan-v2')
archive(Path('/tmp/mcfta-cluster-admission-outer-declaration-v2-audit'), 'outer-declaration-v2-audit')
archive(owner, 'outer-declaration-plan-v3')
archive(review, 'outer-declaration-v3-audit')
save('root-outer-declaration-gate.json', {
    'status': 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    'module': 'SourceCurrentOriginalRowClusterAdmission',
    'public_heads': ['cluster_complete', 'completed_admitted'],
    'contracts_sha256': sha(owner / 'contracts.json'), 'contracts_count': 11,
    'root_complete_context_public_local_obtain_and_IH_read': True,
    'independent_review_sha256': sha(review / 'review.json'),
    'source_target': [180, 220], 'whole_source_hard_stop': 230,
    'body_authoring_authorized': True, 'compiler_activation_authorized': False,
    'dependency_before_compiler': 'The selected boundary source must separately pass strict, sole FULL, complete TYPE acceptance, installation and focused build.',
    'default_declaration_limits': True, 'all_linters': True,
    'scope': 'Actual completion from the current packet; final At and canonical pair admission. The observed adapter derives exact full-state equality across fuel before certificate transport.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: exact outer producer/observed-adapter declarations accepted before body; cap230')
