import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
prep = HERE / 'full-preparation-v2'
source = (HERE / 'SourceCurrentColdFiniteWarmCalls.lean').read_bytes()
printer = (prep / 'cold-finite-calls-full-printer.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
assert hashlib.sha256(printer).hexdigest() == 'a0a6d1dd326c17cb4c46bae03a5e1f797df6e8030554d8576a03fd64eb39f160'
assert printer.startswith(source) and len(printer.splitlines()) == 171
assert source == (HERE / 'cold-finite-calls-strict-2.source.lean').read_bytes()
assert json.loads((HERE / 'cold-finite-calls-strict-2.json').read_text())['exit_code'] == 0
assert (HERE / 'cold-finite-calls-strict-2.log').read_bytes() == b''
report = HERE / 'full-preparation-v2-audit/review.md'
assert report.is_file() and not (HERE / 'cold-finite-calls-public-2.json').exists()
assert json.loads((HERE / 'rejected-v1-public-type-review.json').read_text())['status'] == 'REJECTED_PUBLIC_TYPE_HYGIENE'
pins = {
    'cold-finite-calls-check-full-public.py': ('53dc253311d538f01678ceb6623f5397fa1f84c2d8919dcaac69e0f058166183', '4daead2c07b238508524d2f366eba273f1ca8a673146090ebcf288075d13b8d4'),
    'read-full.py': ('cc80826b1704d5e624f77a2e82fe3627258df4b427dd38b6b08db940ae4847cd', '99a796d4114e43da1f218bba90cac5bff57945841824a28885a8c27e28eac284'),
    'verify-preservation.py': ('1c35b398b09c6905870a0715906bf526756de465000da923cfc2c71d1c936b25', '66965247bd2be685cd35996756c53a92e8022e212e892530bfd07ae20e486f1a'),
}
for name, (old, new) in pins.items():
    data = (prep / name).read_bytes()
    assert hashlib.sha256((HERE / name).read_bytes()).hexdigest() == old
    assert hashlib.sha256(data).hexdigest() == new
    (HERE / name).write_bytes(data)
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    root_whole_printer_helpers_and_deltas='CLEAR', independent_whole_review='CLEAR',
    independent_report_sha256=hashlib.sha256(report.read_bytes()).hexdigest(),
    source_sha256=hashlib.sha256(source).hexdigest(), printer_sha256=hashlib.sha256(printer).hexdigest(),
    activated_helper_pins=pins, selected_job='cold-finite-calls-public-2',
    sole_FULL_for_revised_source_authorized=True, old_FULL1_rejected_and_retained=True,
    all_privacy_and_public_instance_checks_retained=True, declaration_limits_unchanged=True,
    diagnostic_limits_after_ended_module_only=True, accepted_TYPE_requires_literal_byte_identity=True)
(HERE / 'root-full-preparation-v2-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
