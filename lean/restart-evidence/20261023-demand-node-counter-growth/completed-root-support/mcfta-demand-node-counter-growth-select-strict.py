exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))

receipt = load(HERE / 'strict1.json')
source = HERE / 'strict1.source.lean'
assert receipt['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
assert sha(source) == receipt['sha256'] == 'c94db7eee4e7aa54d00f30ed4703301e5b4b5cefb106c1c619cc95994d3676f0'
assert source.read_bytes() == (HERE / 'variants/v1' / (NAME + '.lean')).read_bytes()
assert len(source.read_bytes().splitlines()) == 80
assert receipt['command'][1:] == ['-Dlinter.all=true', str(source)]
assert load(HERE / 'strict1.limits.json') == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
assert load(HERE / 'root-body-gate-v1.json')['compiler_activation_authorized']
assert not (HERE / (NAME + '.lean')).exists()
save('selected-source-gate.json', dict(status='ACCEPTED_STRICT_SOURCE', module=NAME,
    source_sha256=sha(source), source_lines=80, source_cap=160, selected_strict='strict1', strict_log_bytes=0,
    public_heads=['step_mono', 'execute_mono', 'resume_mono'], receipt_sha256=sha(HERE / 'strict1.json'),
    root_default_limit_check=True, all_linters=True, declaration_gate='root-declaration-gate.json',
    body_gate='root-body-gate-v1.json', canonical_copy_deferred_to_reviewed_materializer=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('Accepted strict1 with an empty log. The reviewed materializer will create the canonical evidence source.')
