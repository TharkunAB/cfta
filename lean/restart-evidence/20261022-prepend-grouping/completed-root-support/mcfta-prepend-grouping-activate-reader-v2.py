import hashlib
import json
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-prepend-grouping')
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
prep = here / 'full-preparation-v2'
pins = json.loads((prep / 'pins.json').read_text())
assert isinstance(pins, dict) and len(pins) == 37
for name, pin in pins.items():
    path = prep / name
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], name
assert sha(here / 'full-tool-audit-v2/review.md') == '01b957deff1e16954d6d86699f6d2de7e44e97cc47c3a75d53b17b4900efefb2'
assert sha(prep / 'check-full-public.py') == '3f88ecfe2662cc630dc73caee5c3862970f51e405344e2d6e14f29c82de9459e'
assert sha(here / 'check-full-public.py') == '53ad8cc4f0cfa01ee0341f7d7ea62bced10b068d20584058104a26509a2345ad'
assert sha(here / 'SourceCurrentPrependGrouping.lean') == '3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba'
assert sha(here / 'prepend-grouping-public-1.source.lean') == '0744a37546ea7fa5c6576dd5cf4b6268137219fe68829438f0a8c54e31332015'
assert sha(here / 'prepend-grouping-public-1.log') == '215b81824a227e47375a236476dd83092a5bf1c21a421a85e835bdd3e75e61a8'
assert not (here / 'public-readback').exists()
assert json.loads((here / 'prepend-grouping-public-1.json').read_text())['exit_code'] == 0
assert json.loads((prep / 'actual-failed-reader-1/mcfta-prepend-grouping-read-full-1.json').read_text())['exit_code'] == 1
target = here / 'check-full-public-v2.py'
assert not target.exists()
target.write_bytes((prep / 'check-full-public.py').read_bytes())
gate = dict(status='ROOT_SOURCE_AND_INDEPENDENT_READER_REVIEW_CLEAR', reader_sha256=sha(target),
    source_and_full_unchanged=True, sole_full='prepend-grouping-public-1',
    old_failed_reader_retained=True, root_whole_reader_read=True,
    comparison='Collapse ASCII space/tab/CR/LF runs only; retain both raw TYPEs and actual byte identity.',
    new_lean_jobs_authorized=0)
(here / 'root-reader-v2-review.json').write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(gate))
