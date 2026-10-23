exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-cluster-admission-boundary-source-v2')
review = Path('/tmp/mcfta-cluster-admission-boundary-body-v2-audit')
checked_package(owner, 'cceb3fed533ca4f962a0bbe5718cade28367206b229ce4294c499d1fb3391472', 'df87364c087a2e620d515e51a93448620647b5f4853cd7c4a7365cb4195d4b59')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
source = owner / 'SourceCurrentOriginalRowClusterAdmissionBoundary.lean'
assert sha(source) == 'dbf021c085481ed1b91755ceaa9ac8e0abb8c4d3eaab1b4c9b1d69089e3f1db2'
assert len(source.read_text().splitlines()) == 199
new = (HERE / 'boundary-source-v1/SourceCurrentOriginalRowClusterAdmissionBoundary.lean').read_text()
for name in ['context.lean.txt', 'local-parentAdmitted.lean.txt']:
    new = new.replace((HERE / 'boundary-declaration-plan' / name).read_text().rstrip('\n'),
        (HERE / 'boundary-declaration-v2' / name).read_text().rstrip('\n'))
assert source.read_text() == new
assert load(HERE / 'root-boundary-declaration-v2-gate.json')['body_authoring_authorized']
assert load(HERE / 'boundary-strict1.json')['exit_code'] == 1
archive(owner, 'boundary-source-v2')
archive(review, 'boundary-body-v2-audit')
save('root-boundary-v2-body-gate.json', {
    'status': 'ACCEPTED_SOURCE_BODY_FOR_STRICT', 'source_sha256': sha(source), 'source_lines': 199,
    'root_complete_source_and_exact_two_line_delta_read': True,
    'independent_body_review_sha256': sha(review / 'review.json'),
    'declaration_gate': 'root-boundary-declaration-v2-gate.json',
    'whole_source_hard_stop': 230,
    'strict_compiler_activation_authorized': True, 'FULL_activation_authorized': False,
    'default_declaration_limits': True, 'all_linters': True,
    'v1_source_and_failed_strict_evidence_retained': True,
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: complete revised boundary accepted for strict2; all prior history retained')
