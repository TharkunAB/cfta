import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
name = 'SourceCurrentSameSymbolEdgeForwardCompletion'
source = (HERE / 'same-symbol-edge-forward-strict-3.source.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'c1b7480244632c2cc0454051f0dc7f63649d9ed4cf3c2548edf615ff8647aafd'
assert len(source.splitlines()) == 216
assert json.loads((HERE / 'same-symbol-edge-forward-strict-3.json').read_text())['exit_code'] == 0
assert (HERE / 'same-symbol-edge-forward-strict-3.log').read_bytes() == b''
context = (HERE / 'forward-plan-v2/context.lean.txt').read_bytes()
header = (HERE / 'forward-plan-v2/proposed-signature.lean.txt').read_bytes()
assert source.startswith(context)
start = source.index(b'theorem both_miss_complete ')
assert source[start:source.index(b' := by', start)] + b'\n' == header
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
head = 'MicroCFTA.' + name + '.both_miss_complete'
tail = '\n' + ''.join('set_option ' + option + '\n' for option in options)
tail += ''.join(command + head + '\n' for command in ['#check @', '#print ', '#print axioms '])
assert len(tail.splitlines()) == 14
snapshot, printer = HERE / (name + '.lean'), HERE / 'full-preparation' / (name + '.full.lean')
assert not snapshot.exists() and not printer.exists()
snapshot.write_bytes(source)
printer.write_bytes(source + tail.encode())
print(json.dumps({'status': 'PASS', 'source_sha256': hashlib.sha256(source).hexdigest(),
    'printer_sha256': hashlib.sha256(printer.read_bytes()).hexdigest(),
    'source_lines': 216, 'printer_lines': len(printer.read_bytes().splitlines()), 'diagnostic_tail_lines': 14}))
