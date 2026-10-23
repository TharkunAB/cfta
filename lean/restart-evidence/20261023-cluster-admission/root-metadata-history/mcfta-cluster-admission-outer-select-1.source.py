exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
stem = 'outer-strict1'
receipt = load(HERE / (stem + '.json'))
assert receipt['exit_code'] == 0 and receipt['sha256'] == '13d2fc71f5cb29a0c836954a2bec01de7d3569eff0797a6bda2ad7ca00374bc1'
assert sha(HERE / receipt['source']) == receipt['sha256']
assert (HERE / (stem + '.log')).read_bytes() == b''
assert '-Dlinter.all=true' in receipt['command']
assert load(HERE / (stem + '.limits.json')) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
assert load(HERE / 'root-outer-dependency-ready-gate.json')['compiler_activation_authorized']
save('outer-selected-source-gate.json', {
    'status': 'ACCEPTED_STRICT_SOURCE', 'source_sha256': receipt['sha256'],
    'source_lines': 136, 'selected_strict': stem, 'strict_log_bytes': 0,
    'receipt_sha256': sha(HERE / (stem + '.json')),
    'declaration_gate': 'root-outer-declaration-gate.json',
    'body_gate': 'root-outer-body-gate.json',
    'dependency_gate': 'root-outer-dependency-ready-gate.json',
    'source_cap': 230, 'public_heads': ['cluster_complete', 'completed_admitted'],
    'FULL': 'One sole run after exact tool review and installation.',
    'history': 'Outer strict1 passed unchanged reviewed V1 body; no outer FULL yet.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: actual outer strict1 exit0 and literal-empty log accepted')
