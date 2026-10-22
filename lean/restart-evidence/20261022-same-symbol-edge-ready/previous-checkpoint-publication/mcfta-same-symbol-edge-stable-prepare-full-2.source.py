import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
name = 'SourceCurrentSameSymbolEdgeStable'
source = (HERE / 'same-symbol-edge-stable-strict-4.source.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == '6c96e7e8d5cb32d1209818ed65de83a5104b6a409d65b9caffb52d802e874b91'
assert len(source.splitlines()) == 338
assert json.loads((HERE / 'same-symbol-edge-stable-strict-4.json').read_text())['exit_code'] == 0
assert (HERE / 'same-symbol-edge-stable-strict-4.log').read_bytes() == b''
context = (HERE / 'stable-plan/context.lean.txt').read_bytes()
header = (HERE / 'stable-plan/proposed-signature.lean.txt').read_bytes()
assert source.startswith(context)
start = source.index(b'theorem completed_preserves ')
header_start = source.rfind(b'/--', 0, start)
assert source[header_start:source.index(b' := by', start) + len(b' := by\n')] == header
stable_start = source.index(b'structure Stable ')
stable = source[stable_start:source.index(b'\n\n/-!', stable_start)] + b'\n'
assert stable == (HERE / 'source-author-v2/contract/documented-stable.lean.txt').read_bytes()
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
head = 'MicroCFTA.' + name + '.completed_preserves'
tail = '\n' + ''.join('set_option ' + option + '\n' for option in options)
tail += ''.join(command + head + '\n' for command in ['#check @', '#print ', '#print axioms '])
assert len(tail.splitlines()) == 14
snapshot, printer = HERE / (name + '.lean'), HERE / 'full-preparation' / (name + '.full.lean')
assert not snapshot.exists() and not printer.exists()
old = (HERE.parent / '20261022-same-symbol-edge-forward-completion/prepare-selected-full.py').read_bytes()
(HERE / 'prepare-selected-full.H8-original.py.txt').write_bytes(old)
(HERE / 'prepare-selected-full.patch').write_text(''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), Path(__file__).read_text().splitlines(keepends=True), fromfile='H8-prepare-selected-full', tofile='H9-prepare-selected-full')))
snapshot.write_bytes(source)
printer.write_bytes(source + tail.encode())
print(json.dumps({'status': 'PASS', 'source_sha256': hashlib.sha256(source).hexdigest(),
    'printer_sha256': hashlib.sha256(printer.read_bytes()).hexdigest(),
    'source_lines': 338, 'printer_lines': len(printer.read_bytes().splitlines()), 'diagnostic_tail_lines': 14}))
