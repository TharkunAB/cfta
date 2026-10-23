exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
boundary = 'SourceCurrentOriginalRowClusterAdmissionBoundary'
source = ROOT / 'lean/MicroCFTA' / (boundary + '.lean')
accepted = load(HERE / 'root-boundary-full-review.json')
assert accepted['status'] == 'ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED'
assert sha(source) == accepted['source_sha256']
build = load(HERE / 'boundary-build1.json')
assert build['exit_code'] == 0 and build['command'][-1] == 'MicroCFTA.' + boundary
assert load(HERE / 'boundary-build1.limits.json') == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
artifact = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA' / (boundary + '.olean')
assert artifact.is_file()
body = load(HERE / 'root-outer-body-gate.json')
assert body['status'] == 'ACCEPTED_EXACT_BODY_PENDING_BOUNDARY_DEPENDENCY_READINESS'
outer = HERE / 'outer-source-v1/SourceCurrentOriginalRowClusterAdmission.lean'
assert sha(outer) == body['source_sha256']
save('root-outer-dependency-ready-gate.json', {
    'status': 'ACCEPTED_BOUNDARY_READY_FOR_OUTER_STRICT',
    'boundary_source_sha256': sha(source),
    'boundary_full_review_sha256': sha(HERE / 'root-boundary-full-review.json'),
    'boundary_build_receipt_sha256': sha(HERE / 'boundary-build1.json'),
    'boundary_artifact_sha256': sha(artifact),
    'outer_source_sha256': sha(outer),
    'outer_body_gate_sha256': sha(HERE / 'root-outer-body-gate.json'),
    'compiler_activation_authorized': True,
    'authorized_next_job': 'outer-strict1',
    'new_proof_result_claimed': False,
})
print('PASS: boundary accepted, installed and built; exact outer strict source authorized')
