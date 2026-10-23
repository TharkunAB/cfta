exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
receipt = load(HERE / 'strict1.json')
assert receipt['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
source = HERE / 'strict1.source.lean'
assert sha(source) == receipt['sha256'] == '2dc66e6e7cc728b051a65d622f6aab9bd236ac485b90eb4c1f60650fc438d16a'
assert source.read_bytes() == (HERE / 'variants/v1' / (NAME + '.lean')).read_bytes()
assert len(source.read_bytes().splitlines()) == 82
assert receipt['command'][1:] == ['-Dlinter.all=true', str(source)]
assert load(HERE / 'strict1.limits.json') == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
assert load(HERE / 'root-body-gate-v1.json')['compiler_activation_authorized']
target = HERE / (NAME + '.lean')
assert not target.exists()
target.write_bytes(source.read_bytes())
save('selected-source-gate.json', dict(status='ACCEPTED_STRICT_SOURCE', module=NAME,
    source_sha256=sha(source), source_lines=82, source_cap=160, selected_strict='strict1', strict_log_bytes=0,
    public_heads=['execute_mono','unfold_mono','maybeMu_mono'], receipt_sha256=sha(HERE / 'strict1.json'),
    root_default_limit_check=True, all_linters=True,
    declaration_gate='root-declaration-gate.json', body_gate='root-body-gate-v1.json',
    goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED strict1 with an empty log; exact82-line canonical evidence source copied, live module not installed.')
