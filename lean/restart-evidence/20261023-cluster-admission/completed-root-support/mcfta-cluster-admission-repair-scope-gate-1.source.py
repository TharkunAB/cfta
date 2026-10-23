exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-cluster-admission-proof-verifier-v2-repair-plan')
checked_package(plan, 'e8e9898f4205e1b6f2f44bf4bbd30c5017845b457807b280e71876bc6d67845a', 'e8cc5e138433288a16da010f4975e2be93f9f1b85e2630e2c39b1bde5e0bfd41')
old = Path('/tmp/mcfta-cluster-admission-proof-verifier-preparation')
checked_package(old, '5c382275760f0ea32582e746c30dbd4e17b08e1a73e7d2f49bd4d1596bc33932', 'b513d2cd8b638417032ed59f846acdba0ebd9d069850c735bd1ceccb4b69e0b5')
audit = Path('/tmp/mcfta-cluster-admission-proof-verifier-audit')
checked_package(audit, '23568b2528dc117c7c1055376ccd883a8d0103bbd3c4167dad2dedab7598d472', 'efbe1b3b6ec75a78c4a8f0dd70c09e21806d6851d7287bfb99c070237cbf10cb')
review = load(audit / 'review.json')
assert review['status'] == 'SOURCE_ONLY_HOLD_TWO_CONFIRMED_BLOCKERS'
assert len(review['blockers']) == 2 and not review['additional_blocker_found']
assert not review['prepared_execution']
archive(old, 'proof-verifier-preparation-v1')
archive(audit, 'proof-verifier-v1-audit')
archive(plan, 'proof-verifier-v2-repair-plan')
save('root-proof-verifier-v2-repair-scope-gate.json', dict(
    status='ACCEPTED_SOURCE_ONLY_REPAIR_SCOPE_BEFORE_V2_AUTHORING',
    plan_sha256=sha(plan / 'plan.md'),
    independent_v1_review_sha256=sha(audit / 'review.json'),
    independent_plan_review='Arity source-only whole plan and four pins clear at 09:04 CEST.',
    source_line_cap=450, root_whole_v1_code_lines_read=385,
    root_whole_v1_bound_data_lines_read=1119,
    allowed_code_delta='Use a column-preserving bullet-to-spaces view only for local fragment count, index and order. Keep all raw source guards unchanged.',
    allowed_data_delta='Bind the independently reviewed actual history revision that removes only six duplicate artifact records.',
    variant_artifact_disjointness_guard_unchanged=True,
    v1_immutable_and_unexecuted=True, selected_v2_authoring_accepted=True,
    execution_accepted=False, mathematical_sources_unchanged=True))
print('ACCEPTED source-only V2 repair scope; execution remains blocked pending final independent review.')
