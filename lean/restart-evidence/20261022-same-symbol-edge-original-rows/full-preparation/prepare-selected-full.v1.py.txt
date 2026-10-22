import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
stem, expected_sha, expected_lines = sys.argv[1:]
name = 'SourceCurrentSameSymbolEdgeOriginalRows'
source = (HERE / (stem + '.source.lean')).read_bytes()
assert hashlib.sha256(source).hexdigest() == expected_sha
assert len(source.splitlines()) == int(expected_lines) and 1 <= int(expected_lines) <= 250
assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
context = (HERE / 'full-preparation/context.lean.txt').read_bytes()
proposed = (HERE / 'full-preparation/proposed-signature.lean.txt').read_bytes()
header = proposed.rstrip(b'\n') + b' := by\n'
assert source.startswith(context + header)
assert len(context.splitlines()) == 19 and len(header.splitlines()) == 54
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert b'set_option maxRecDepth' not in source and b'set_option maxHeartbeats' not in source
options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
head = 'MicroCFTA.' + name + '.both_miss_complete'
tail = '\n' + ''.join('set_option ' + option + '\n' for option in options)
tail += ''.join(command + head + '\n' for command in ['#check @', '#print ', '#print axioms '])
assert len(tail.splitlines()) == 14
assert tail.encode() == (HERE / 'full-preparation/diagnostic-tail.lean.txt').read_bytes()
snapshot = HERE / (name + '.lean')
printer = HERE / (name + '.full.lean')
assert not snapshot.exists() and not printer.exists()
snapshot.write_bytes(source)
printer.write_bytes(source + tail.encode())
(HERE / 'actual-header.lean.txt').write_bytes(header)
print(json.dumps({'status': 'PASS', 'source_sha256': expected_sha,
    'printer_sha256': hashlib.sha256(printer.read_bytes()).hexdigest(),
    'source_lines': int(expected_lines), 'printer_lines': len(printer.read_bytes().splitlines()),
    'context_lines': 19, 'actual_header_lines': 54,
    'actual_header_sha256': hashlib.sha256(header).hexdigest(),
    'diagnostic_tail_lines': 14, 'selected_strict': stem}))
