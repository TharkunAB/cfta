import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
stem, expected_sha, expected_lines = sys.argv[1:]
name = 'SourceCurrentSameSymbolEdgeReady'
source = (HERE / (stem + '.source.lean')).read_bytes()
assert hashlib.sha256(source).hexdigest() == expected_sha
assert len(source.splitlines()) == int(expected_lines)
assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
context = (HERE / 'ready-plan/context.lean.txt').read_bytes()
header = (HERE / 'ready-plan/proposed-signature.lean.txt').read_bytes()
assert source.startswith(context) and source.count(header) == 1
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
head = 'MicroCFTA.' + name + '.ready_complete'
tail = '\n' + ''.join('set_option ' + option + '\n' for option in options)
tail += ''.join(command + head + '\n' for command in ['#check @', '#print ', '#print axioms '])
assert len(tail.splitlines()) == 14
snapshot = HERE / (name + '.lean')
printer = HERE / (name + '.full.lean')
assert not snapshot.exists() and not printer.exists()
snapshot.write_bytes(source)
printer.write_bytes(source + tail.encode())
print(json.dumps({'status': 'PASS', 'source_sha256': expected_sha,
    'printer_sha256': hashlib.sha256(printer.read_bytes()).hexdigest(),
    'source_lines': int(expected_lines), 'printer_lines': len(printer.read_bytes().splitlines()),
    'diagnostic_tail_lines': 14, 'selected_strict': stem}))
