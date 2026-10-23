exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
source = HERE / 'strict-selected-source.lean'
receipt = HERE / 'strict1.json'
assert load(receipt)['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
assert source.read_bytes() == (HERE / 'strict1.source.lean').read_bytes()
assert sha(source) == '355224ff767c10856684db24c0d6393e61c63a6754ae6044bb64ba29b0ca61e7'
assert load(HERE / 'root-v1-body-gate.json')['compiler_activation_authorized']
assert not (HERE / (NAME + '.lean')).exists()
save('selected-source-gate.json', dict(status='ACCEPTED_STRICT_SOURCE', module=NAME,
    source_sha256=sha(source), source_lines=90, source_cap=180, public_heads=['rebuilt_admitted'],
    selected_strict='strict1', strict_log_bytes=0, receipt_sha256=sha(receipt),
    declaration_gate='root-declaration-gate.json', body_gate='root-v1-body-gate.json',
    root_default_limit_check=True, all_linters=True, compiler_jobs=1, failed_jobs=0))
print('ACCEPTED strict1 with an empty raw log; canonical materializer snapshot remains absent.')
