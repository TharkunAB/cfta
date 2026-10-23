exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
receipt = load(HERE / 'boundary-strict3.json')
source = HERE / receipt['source']
assert receipt['exit_code'] == 0 and (HERE / receipt['log']).read_bytes() == b''
assert sha(source) == receipt['sha256'] == 'd610d762a429313d324e6184265d793312a2e8ac05d24c936dc350a4b5be8b93'
assert source.read_bytes() == (HERE / 'boundary-source-v3/SourceCurrentOriginalRowClusterAdmissionBoundary.lean').read_bytes()
assert load(HERE / 'root-boundary-v3-body-gate.json')['strict_compiler_activation_authorized']
assert load(HERE / receipt['limits']) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
assert '-Dlinter.all=true' in receipt['command']
assert not any('maxHeartbeats' in arg or 'maxRecDepth' in arg for arg in receipt['command'])
save('boundary-selected-source-gate.json', {
    'status': 'ACCEPTED_STRICT_SOURCE', 'source_sha256': sha(source), 'source_lines': 199,
    'selected_strict': 'boundary-strict3', 'strict_log_bytes': 0,
    'receipt_sha256': sha(HERE / 'boundary-strict3.json'),
    'declaration_gate': 'root-boundary-declaration-v3-gate.json',
    'body_gate': 'root-boundary-v3-body-gate.json',
    'source_cap': 230, 'public_heads': ['boundary_complete'],
    'FULL': 'One sole run for this variant, after exact V3 tool review and installation.',
    'history': 'Actual strict1 failed on V1 notation; strict2 failed on V2 projection notation; strict3 passed on V3. No boundary FULL yet.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: selected boundary strict3 is clean at default declaration limits and exact reviewed bytes')
