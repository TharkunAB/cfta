exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
stem = 'root-pair-node-counter-growth-strict-1'
source = HERE / (stem + '.source.lean')
receipt = load(HERE / (stem + '.json'))
assert receipt['exit_code'] == 0 and receipt['observed_at']
assert sha(source) == receipt['sha256'] == '6cfaf5e340d26b8c838f51d93fb3ae0e03b098510ca41b5021ada4e96b72c2e8'
assert source.read_bytes() == (HERE / 'root-body-v1.lean').read_bytes()
assert len(source.read_bytes().splitlines()) == 96
assert receipt['source'] == source.name and Path(receipt['command'][-1]) == source
assert '-Dlinter.all=true' in receipt['command']
assert (HERE / receipt['log']).read_bytes() == b''
assert load(HERE / receipt['limits']) == {'memory.max':'4294967296', 'memory.high':'4294967296', 'memory.swap.max':'0'}
usage = load(HERE / (stem + '.usage.json'))
assert usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
assert load(HERE / 'root-body-gate.json')['first_strict_authorized']
assert b'set_option' not in source.read_bytes()
save('selected-source-gate.json', dict(status='ACCEPTED_STRICT_SOURCE', module=NAME,
    source_sha256=sha(source), source_lines=96, source_cap=160, selected_strict=stem,
    strict_log_bytes=0, public_heads=['outcomeState','step_mono','execute_mono'],
    public_kinds=[['outcomeState','def'],['step_mono','theorem'],['execute_mono','theorem']],
    receipt_sha256=sha(HERE / (stem + '.json')), root_default_limit_check=True,
    all_linters=True, declaration_gate='root-declaration-gate.json', body_gate='root-body-gate.json',
    canonical_copy_deferred_to_reviewed_materializer=True, goal_status='ACTIVE_INCOMPLETE'))
print('Selected the actual first clean strict source; no canonical or public output was written.')
