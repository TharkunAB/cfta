exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import re
source = HERE / 'strict1.source.lean'
receipt = load(HERE / 'strict1.json')
assert receipt['exit_code'] == 0 and receipt['observed_at']
assert receipt['sha256'] == sha(source) == 'b7351e92c6981f5caa5d7a18a05676912b9ee741c94cc2a39f1ba3ef74b03840'
assert receipt['source'] == source.name and receipt['command'][1] == '-Dlinter.all=true'
assert Path(receipt['command'][-1]) == source
assert (HERE / 'strict1.log').read_bytes() == b''
assert source.read_bytes() == (HERE / 'source-v1' / (NAME + '.lean')).read_bytes()
assert len(source.read_bytes().splitlines()) == 77 <= 180
assert not re.search(rb'(?m)^\s*set_option\s+(?:maxHeartbeats|maxRecDepth|linter\.)', source.read_bytes())
save('selected-source-gate.json', dict(status='ACCEPTED_STRICT_SOURCE', module=NAME,
    source_sha256=sha(source), source_lines=77, source_cap=180, selected_strict='strict1',
    strict_log_bytes=0, public_heads=['rebase'], receipt_sha256=sha(HERE / 'strict1.json'),
    declaration_gate='root-declaration-gate.json', body_gate='root-v1-body-gate.json',
    root_default_limit_check=True, all_linters=True))
print('SELECTED strict1:77 lines, raw empty log, unchanged source, default limits and all linters.')
