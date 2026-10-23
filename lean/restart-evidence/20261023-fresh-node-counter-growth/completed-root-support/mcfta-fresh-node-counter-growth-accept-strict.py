exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import sys
stem = sys.argv[1]
body = load(HERE / 'root-body-gate.json')
assert body['status'] == 'ACCEPTED_COMPLETE_BODY_BEFORE_STRICT'
assert body['compiler_activation_authorized']
receipt = load(HERE / (stem + '.json'))
source = HERE / (stem + '.source.lean')
assert receipt['exit_code'] == 0 and receipt['observed_at']
assert receipt['source'] == source.name and receipt['sha256'] == sha(source) == body['source_sha256']
assert source.read_bytes() == (HERE / body['source']).read_bytes()
assert receipt['command'][1] == '-Dlinter.all=true' and Path(receipt['command'][-1]) == source
assert receipt['log'] == stem + '.log' and (HERE / receipt['log']).read_bytes() == b''
assert load(HERE / (stem + '.limits.json')) == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
usage = load(HERE / (stem + '.usage.json'))
assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
save('selected-source-gate.json', dict(status='ACCEPTED_STRICT_SOURCE',module=NAME,
    source_sha256=sha(source),source_lines=len(source.read_bytes().splitlines()),source_cap=180,
    selected_strict=stem,strict_log_bytes=0,public_heads=body['public_heads'],
    receipt_sha256=sha(HERE / (stem+'.json')),root_default_limit_check=True,all_linters=True,
    declaration_gate='root-declaration-gate.json',body_gate='root-body-gate.json',
    goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED actual strict source: exit 0, empty log, default limits, all linters, owned capped receipt.')
