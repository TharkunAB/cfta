exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-cluster-admission-execution-plan')
review = Path('/tmp/mcfta-cluster-admission-execution-plan-audit')
checked_package(owner, 'f66cb2934364aacba28d830037ebd57e8b1bdd50d18d7c7751a740751715d348', 'fb89ae27988603ce89e21fa29a201a97e1ff4e8fadb44ce099bf248cce1f3572')
checked_package(review, '52a478194100aa891aa014501ce62b9602604b23c25755f18019be8acb7b6d01', '6d6bbf7913d0d8e4b7b890206e1097481431229a9b2be52388e6df9d109a5538')
audit = load(review / 'review.json')
assert audit['status'] == 'CLEAR' and not audit['reviewer_plan_author']
contracts = load(owner / 'contracts.json')
for name, pin in contracts.items():
    assert sha(owner / name) == pin['sha256']
    assert len((owner / name).read_text().splitlines()) == pin['lines']
index = load(owner / 'source-index.json')
for item in index:
    assert sha(ROOT / item['source']) == item['sha256']
archive(owner, 'execution-declaration-plan')
archive(review, 'execution-declaration-audit')
save('root-execution-declaration-gate.json', {
    'status': 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    'module': NAME, 'public_heads': audit['public_heads'],
    'contracts_sha256': sha(owner / 'contracts.json'),
    'root_complete_context_headers_local_types_and_IH_read': True,
    'independent_review_sha256': sha(review / 'review.json'),
    'attribution_correction': 'Root authored the operational plan. The frozen review prose incorrectly says Arity; reviewer_plan_author=false is correct.',
    'whole_source_hard_stop': 130, 'target': [90, 115],
    'default_declaration_limits': True, 'all_linters': True,
    'mathematical_body_authoring_authorized': True,
    'compiler_activation_authorized': False,
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: exact operational declarations accepted before body; hard stop130; compiler inactive')
