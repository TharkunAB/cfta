import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
stem, expected_sha, expected_lines, expected_context_sha, expected_context_lines, expected_signature_sha, expected_signature_lines = sys.argv[1:]
assert all(len(value) == 64 and set(value) <= set('0123456789abcdef') for value in [expected_sha, expected_context_sha, expected_signature_sha])
name = '__H24_MODULE_NAME__'
source = (HERE / (stem + '.source.lean')).read_bytes()
assert hashlib.sha256(source).hexdigest() == expected_sha
assert len(source.splitlines()) == int(expected_lines) and 1 <= int(expected_lines) <= int("__H24_SOURCE_HARD_STOP__")
assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
context = (HERE / 'signature-plan/context.lean.txt').read_bytes()
proposed = (HERE / 'signature-plan/public-header.lean.txt').read_bytes()
assert source.startswith(context)
assert hashlib.sha256(context).hexdigest() == expected_context_sha
assert hashlib.sha256(proposed).hexdigest() == expected_signature_sha
assert len(context.splitlines()) == int(expected_context_lines) >= 1
assert len(proposed.splitlines()) == int(expected_signature_lines) >= 1
specs = [tuple(spec) for spec in json.loads('__H24_PUBLIC_SPECS_JSON__')]
markers = list(re.finditer(rb'(?m)^/--[^\n]*-/\n(def|theorem) ([^\s(\[{:=]+)', proposed))
assert [(m.group(2).decode(), m.group(1).decode()) for m in markers] == specs
headers, positions = [], []
for index, marker in enumerate(markers):
    end = markers[index + 1].start() if index + 1 < len(markers) else len(proposed)
    header = proposed[marker.start():end].rstrip(b'\n') + (b' :=\n' if specs[index][1] == 'def' else b' := by\n')
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
assert len(tail.splitlines()) == 11 + 3 * len(specs)
assert tail.encode() == (HERE / 'full-preparation/diagnostic-tail.lean.txt').read_bytes()
snapshot = HERE / (name + '.lean')
printer = HERE / (name + '.full.lean')
assert not snapshot.exists() and not printer.exists() and not (HERE / 'actual-header.lean.txt').exists()
snapshot.write_bytes(source)
printer.write_bytes(source + tail.encode())
(HERE / 'actual-header.lean.txt').write_bytes(b'\n'.join(headers))
print(json.dumps({'status': 'PASS', 'source_sha256': expected_sha,
    'printer_sha256': hashlib.sha256(printer.read_bytes()).hexdigest(),
    'source_lines': int(expected_lines), 'printer_lines': len(printer.read_bytes().splitlines()),
    'context_lines': int(expected_context_lines), 'actual_header_lines': len(b'\n'.join(headers).splitlines()),
    'context_sha256': expected_context_sha, 'proposed_signature_sha256': expected_signature_sha,
    'actual_header_sha256': hashlib.sha256(b'\n'.join(headers)).hexdigest(),
    'diagnostic_tail_lines': len(tail.splitlines()), 'public_heads': [short for short, _kind in specs], 'selected_strict': stem}))
