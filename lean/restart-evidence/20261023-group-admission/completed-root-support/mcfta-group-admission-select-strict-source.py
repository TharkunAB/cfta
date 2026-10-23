exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
source = HERE / (NAME + '.lean')
receipt = HERE / 'strict1.json'
assert load(receipt)['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
assert source.read_bytes() == (HERE / 'strict1.source.lean').read_bytes()
assert sha(source) == '1663238beb7983e2d869730cef3c6c32a02992eb54f4638a9d774b7af2a8ece8'
assert load(HERE / 'root-v1-body-gate.json')['compiler_activation_authorized']
save('selected-source-gate.json', dict(status='ACCEPTED_STRICT_SOURCE', module=NAME,
    source_sha256=sha(source), source_lines=100, source_cap=180, public_heads=['groups_admitted'],
    selected_strict='strict1', strict_log_bytes=0, receipt_sha256=sha(receipt),
    declaration_gate='root-declaration-gate.json', body_gate='root-v1-body-gate.json',
    root_default_limit_check=True, all_linters=True, compiler_jobs=1, failed_jobs=0))
print('ACCEPTED strict1 with an empty raw log under default declaration limits.')
