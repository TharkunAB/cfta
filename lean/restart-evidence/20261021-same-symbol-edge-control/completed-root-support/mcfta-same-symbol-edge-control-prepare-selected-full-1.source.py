import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = (HERE / 'same-symbol-edge-strict-2.source.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == '062815f1619dce95fac323ce8bfdaebdf11252728516503d6e9ac3c87b034141'
assert json.loads((HERE / 'same-symbol-edge-strict-2.json').read_text())['exit_code'] == 0
assert (HERE / 'same-symbol-edge-strict-2.log').read_bytes() == b''
assert source.decode().rstrip().endswith('end MicroCFTA.SourceCurrentSameSymbolEdgeControl')
assert b'set_option' not in source
tail = (HERE / 'full-preparation/same-symbol-edge-diagnostic-tail.lean.txt').read_bytes()
assert hashlib.sha256(tail).hexdigest() == '4d4c601862578f84489c110447b01d09430b0e02954468f60f27deee9d6ba605'
selected = HERE / 'SourceCurrentSameSymbolEdgeControl.lean'
printer = HERE / 'same-symbol-edge-full-printer.lean'
assert not selected.exists() and not printer.exists()
selected.write_bytes(source)
printer.write_bytes(source + tail)
report = dict(source_sha256=hashlib.sha256(source).hexdigest(), source_lines=len(source.splitlines()),
    printer_sha256=hashlib.sha256(source + tail).hexdigest(), printer_lines=len((source + tail).splitlines()),
    source_default_strict_clean=True, diagnostic_limits_after_module_only=True,
    ordinary_jobs_so_far=2, FULL_jobs_so_far=0, official_install=False)
(HERE / 'selected-full-preparation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
