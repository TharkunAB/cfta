import datetime
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
original = (HERE / 'preservation-preparation/verify-preservation.py').read_text()
assert hashlib.sha256(original.encode()).hexdigest() == '85a4194a7e52385eaa7a4ad2220595edbb71c3227dadb8f0ef05b5a52d351cbc'
old = '32cfa9e1a229237dcaf683fe77f588cb2eeb541929f7e4dff33ef2809370183c'
new = '984f34529a1050fd015ba0fb742b39cc38e0b518eaae69801cbde1727578a6bd'
assert original.count(old) == 1
changed = original.replace(old, new)
assert len(changed.splitlines()) == 110
assert hashlib.sha256((HERE / 'SourceCurrentFiniteWarmCalls.lean').read_bytes()).hexdigest() == new
assert (HERE / 'finite-calls-strict-3.log').read_bytes() == b''
assert not (HERE / 'verify-preservation.py').exists()
(HERE / 'verify-preservation.py').write_text(changed)
(HERE / 'preservation-final-pin.patch').write_text(''.join(difflib.unified_diff(
    original.splitlines(True), changed.splitlines(True), fromfile='provisional', tofile='final')))
report = dict(prepared_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    root_whole_original_110_lines_and_delta_review='CLEAR',
    source_sha256=new, verifier_sha256=hashlib.sha256(changed.encode()).hexdigest(),
    source_only_final_pin_revision=True, changed_occurrences=1,
    independent_final_pin_review_required=True, verifier_execution_authorized=False)
(HERE / 'root-preservation-final-pin.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
