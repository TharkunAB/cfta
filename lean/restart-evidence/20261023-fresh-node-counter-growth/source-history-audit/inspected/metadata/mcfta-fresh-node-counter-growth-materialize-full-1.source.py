import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
stem, expected_sha, expected_lines, expected_context_sha, expected_context_lines, expected_contracts_sha, expected_contracts_count = sys.argv[1:]
assert all(len(value) == 64 and set(value) <= set('0123456789abcdef') for value in [expected_sha, expected_context_sha, expected_contracts_sha])
name = 'InternedFreshOrdinaryNodeCounterGrowth'
specs = [('build_mono', 'theorem'), ('buildMany_mono', 'theorem'), ('buildEdges_mono', 'theorem')]
source_path = HERE / (stem + '.source.lean')
source = source_path.read_bytes()
assert hashlib.sha256(source).hexdigest() == expected_sha
assert len(source.splitlines()) == int(expected_lines) and 1 <= int(expected_lines) <= 180
receipt_path = HERE / (stem + '.json')
receipt = json.loads(receipt_path.read_bytes())
assert receipt['exit_code'] == 0 and receipt['observed_at']
assert receipt['sha256'] == expected_sha
assert (receipt_path.parent / receipt['source']).resolve() == source_path.resolve()
assert Path(receipt['command'][-1]).resolve() == source_path.resolve()
assert '-Dlinter.all=true' in receipt['command']
assert (receipt_path.parent / receipt['log']).resolve() == (HERE / (stem + '.log')).resolve()
assert (HERE / (stem + '.log')).read_bytes() == b''
contract_root = HERE / 'declaration-plan-v3'
contracts_raw = (contract_root / 'contracts.json').read_bytes()
assert hashlib.sha256(contracts_raw).hexdigest() == expected_contracts_sha
contracts = json.loads(contracts_raw)
layout_raw = (contract_root / 'insertion-map.json').read_bytes()
assert hashlib.sha256(layout_raw).hexdigest() == 'c328d493b7520e1452a799203e851fa73657b12e8dcdfd633c3106b7470b7763'
layout = json.loads(layout_raw)
assert len(contracts) == int(expected_contracts_count) == 10
for (filename, expected_digest), record in zip(contracts.items(), layout['compiled_fragments'], strict=True):
    fragment = (contract_root / filename).read_bytes()
    assert filename == record['file'] and hashlib.sha256(fragment).hexdigest() == expected_digest == record['sha256']
    assert len(fragment.splitlines()) == record['lines']
gate = json.loads((HERE / 'root-declaration-gate-v3.json').read_bytes())
assert gate['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
assert gate['module'] == name and gate['public_heads'] == [short for short, _kind in specs]
assert gate['contracts_sha256'] == expected_contracts_sha
assert gate['insertion_map_sha256'] == hashlib.sha256(layout_raw).hexdigest()
assert gate['whole_source_hard_stop'] == 180 and gate['default_declaration_limits'] and gate['all_linters']
assert gate['root_all_public_and_private_header_types_read'] and gate['root_all_local_have_let_and_lambda_types_read']
assert gate['root_all_three_recursive_signatures_and_seven_restricted_call_types_read']
assert gate['root_all_23_scoped_introduced_types_read'] and gate['root_all_13_relevant_live_API_cuts_read']
assert gate['root_whole_context_lines_read'] == 8 and gate['root_whole_public_header_lines_read'] == 12
assert gate['root_whole_private_header_lines_read'] == 18 and gate['root_whole_local_compiled_fragment_lines_read'] == 7
assert gate['private_helpers'] == ['work_mono', 'bind_mono', 'request_mono']
assert re.fullmatch(r'[0-9a-f]{64}', gate['independent_review_sha256'])
context = (contract_root / 'context.lean.txt').read_bytes()
assert source.startswith(context)
assert hashlib.sha256(context).hexdigest() == expected_context_sha
assert len(context.splitlines()) == int(expected_context_lines) == 8
headers, positions = [], []
for filename in ['public-build.lean.txt', 'public-many.lean.txt', 'public-edges.lean.txt']:
    header = (contract_root / filename).read_bytes().rstrip(b'\n') + b' := by\n'
    assert source.count(header) == 1 and source.index(header) >= len(context)
    headers.append(header); positions.append(source.index(header))
assert positions == sorted(positions)
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert b'set_option maxRecDepth' not in source and b'set_option maxHeartbeats' not in source
options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
tail = '\n' + ''.join('set_option ' + option + '\n' for option in options)
for short, _kind in specs:
    tail += ''.join(command + 'MicroCFTA.' + name + '.' + short + '\n' for command in ['#check @', '#print ', '#print axioms '])
assert len(tail.splitlines()) == 11 + 3 * len(specs) == 20
assert tail.encode() == (HERE / 'full-preparation/diagnostic-tail.lean.txt').read_bytes()
snapshot = HERE / (name + '.lean')
printer = HERE / (name + '.full.lean')
actual_headers = HERE / 'actual-fresh-node-counter-growth-headers.lean.txt'
assert not snapshot.exists() and not printer.exists() and not actual_headers.exists()
snapshot.write_bytes(source)
printer.write_bytes(source + tail.encode())
actual_headers.write_bytes(b'\n'.join(headers))
print(json.dumps({'status': 'PASS', 'source_sha256': expected_sha,
    'printer_sha256': hashlib.sha256(printer.read_bytes()).hexdigest(),
    'source_lines': int(expected_lines), 'printer_lines': len(printer.read_bytes().splitlines()),
    'context_lines': int(expected_context_lines), 'actual_header_lines': len(b'\n'.join(headers).splitlines()),
    'context_sha256': expected_context_sha, 'contracts_sha256': expected_contracts_sha,
    'actual_header_sha256': hashlib.sha256(b'\n'.join(headers)).hexdigest(),
    'diagnostic_tail_lines': len(tail.splitlines()), 'public_heads': [short for short, _kind in specs], 'selected_strict': stem}))
