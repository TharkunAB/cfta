exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
receipt = load(HERE / 'execution-strict2.json')
source = HERE / receipt['source']
assert receipt['exit_code'] == 0
assert (HERE / receipt['log']).read_bytes() == b''
assert sha(source) == receipt['sha256'] == 'ee67ecabee46dd20e570eba723a816849c6d28f31a9e14d794eb4026a56092bb'
assert source.read_bytes() == (HERE / 'execution-source-v2' / (NAME + '.lean')).read_bytes()
assert load(HERE / 'root-execution-v2-body-gate.json')['strict_compiler_activation_authorized']
limits = load(HERE / receipt['limits'])
assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
assert '-Dlinter.all=true' in receipt['command']
assert not any('maxHeartbeats' in arg or 'maxRecDepth' in arg for arg in receipt['command'])
save('execution-selected-source-gate.json', {
    'status': 'ACCEPTED_STRICT_SOURCE', 'source_sha256': sha(source), 'source_lines': 64,
    'selected_strict': 'execution-strict2', 'strict_log_bytes': 0,
    'receipt_sha256': sha(HERE / 'execution-strict2.json'),
    'declaration_gate': 'root-execution-declaration-gate.json',
    'body_gate': 'root-execution-v2-body-gate.json',
    'source_cap': 130, 'public_heads': ['yielded_add', 'done_stable', 'completed_unique'],
    'FULL': 'One sole run for this variant, only after exact reviewed tool installation.',
    'history': 'Actual strict1 failed on v1; strict2 passed on v2. No FULL yet.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: default-limits all-linter strict2 has literal empty log and exact accepted bytes')
