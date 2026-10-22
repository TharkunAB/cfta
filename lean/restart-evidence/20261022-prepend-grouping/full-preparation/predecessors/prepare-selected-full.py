import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
stem, expected_sha, expected_lines, expected_context_sha, expected_context_lines, expected_signature_sha, expected_signature_lines = sys.argv[1:]
assert all(len(value) == 64 and set(value) <= set('0123456789abcdef') for value in [expected_sha, expected_context_sha, expected_signature_sha])
name = 'SourceCurrentOriginalRowClusterLanguage'
source = (HERE / (stem + '.source.lean')).read_bytes()
assert hashlib.sha256(source).hexdigest() == expected_sha
assert len(source.splitlines()) == int(expected_lines) and 1 <= int(expected_lines) <= 500
assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
context = (HERE / 'signature-plan/context.lean.txt').read_bytes()
proposed = (HERE / 'signature-plan/proposed-signature.lean.txt').read_bytes()
header = proposed.rstrip(b'\n') + b' := by\n'
assert source.startswith(context)
assert source.count(header) == 1
assert source.index(header) >= len(context)
assert hashlib.sha256(context).hexdigest() == expected_context_sha
assert hashlib.sha256(proposed).hexdigest() == expected_signature_sha
assert len(context.splitlines()) == int(expected_context_lines) >= 1
assert len(proposed.splitlines()) == len(header.splitlines()) == int(expected_signature_lines) >= 1
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert b'set_option maxRecDepth' not in source and b'set_option maxHeartbeats' not in source
options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
head = 'MicroCFTA.' + name + '.cluster_complete'
tail = '\n' + ''.join('set_option ' + option + '\n' for option in options)
tail += ''.join(command + head + '\n' for command in ['#check @', '#print ', '#print axioms '])
assert len(tail.splitlines()) == 14
assert tail.encode() == (HERE / 'full-preparation/diagnostic-tail.lean.txt').read_bytes()
snapshot = HERE / (name + '.lean')
printer = HERE / (name + '.full.lean')
assert not snapshot.exists() and not printer.exists() and not (HERE / 'actual-header.lean.txt').exists()
snapshot.write_bytes(source)
printer.write_bytes(source + tail.encode())
(HERE / 'actual-header.lean.txt').write_bytes(header)
print(json.dumps({'status': 'PASS', 'source_sha256': expected_sha,
    'printer_sha256': hashlib.sha256(printer.read_bytes()).hexdigest(),
    'source_lines': int(expected_lines), 'printer_lines': len(printer.read_bytes().splitlines()),
    'context_lines': int(expected_context_lines), 'actual_header_lines': int(expected_signature_lines),
    'context_sha256': expected_context_sha, 'proposed_signature_sha256': expected_signature_sha,
    'actual_header_sha256': hashlib.sha256(header).hexdigest(),
    'diagnostic_tail_lines': 14, 'selected_strict': stem}))
