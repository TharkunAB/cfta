exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-original-row-cluster-admission-boundary-signature')
review = Path('/tmp/mcfta-cluster-admission-boundary-declaration-audit')
checked_package(owner, '5272b1b9cb4efefff36adaeb223542d1b87e81005192c4759ae3c3a0962e6dcf', '06297ecf7872515b80c33205faa0e86135e370e0fb305b7b09e4c2eed397583b')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
contracts = load(owner / 'contracts.json')
assert len(contracts) == 21
for name, digest in contracts.items():
    assert sha(owner / name) == digest
for item in load(owner / 'source-index.json')['sources']:
    assert sha(ROOT / item['path']) == item['sha256']
schema = load(owner / 'declaration-schema.json')
assert schema['private_helpers'] == [] and schema['global_definitions'] == []
assert len(schema['local_have_names']) == 13
assert schema['local_let_names'] == ['nextIncomparable']
assert schema['by_cases_names'] == ['promoted', 'dropped']
archive(owner, 'boundary-declaration-plan')
archive(review, 'boundary-declaration-audit')
save('root-boundary-declaration-gate.json', {
    'status': 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    'module': 'SourceCurrentOriginalRowClusterAdmissionBoundary',
    'public_heads': ['boundary_complete'],
    'contracts_sha256': sha(owner / 'contracts.json'), 'contracts_count': 21,
    'root_complete_context_public_local_obtain_case_and_IH_read': True,
    'independent_review_sha256': sha(review / 'review.json'),
    'source_target': [210, 230], 'whole_source_hard_stop': 230,
    'proposed_260_fallback_accepted': False,
    'body_authoring_authorized': True, 'compiler_activation_authorized': False,
    'scope': 'One actual smaller scan boundary; fixed Inventory.At/native Covered and captured canonical pair admission. No duplicate language, total length, future run, next inventory or resource premise.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: exact boundary contracts accepted before body; hard stop230; no260 fallback activated')
