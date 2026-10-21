import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
prep = HERE / 'full-preparation'
printer = (prep / 'warm-packet-full-printer.lean').read_bytes()
reader = (prep / 'warm-packet-check-full-public.py').read_bytes()
assert hashlib.sha256(printer).hexdigest() == '2fa0e8e568ecc8a2decd9575448cc1ab264c888c018131ec1bd8ef33b293279d'
assert hashlib.sha256(reader).hexdigest() == '95229fc1023967865d5ff2db32e3303e59d8abc43223228573755010bc3ecc5f'
assert printer.startswith((HERE / 'SourceCurrentWarmNextPacket.lean').read_bytes())
assert json.loads((HERE / 'warm-packet-strict-1.json').read_text())['exit_code'] == 0
assert (HERE / 'warm-packet-strict-1.log').read_bytes() == b''
assert not (HERE / 'warm-packet-public-1.json').exists()
assert not (HERE / 'warm-packet-check-full-public.py').exists()
(HERE / 'warm-packet-check-full-public.py').write_bytes(reader)
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    complete_printer_and_reader_root_review='CLEAR', independent_whole_preparation_review='CLEAR',
    source_sha256='13e8373cff925aca8832a47e12514767dd94dbe3fdb8d68bd73b2cdf19246be8',
    printer_sha256=hashlib.sha256(printer).hexdigest(), reader_sha256=hashlib.sha256(reader).hexdigest(),
    sole_full_authorized=True, selected_job='warm-packet-public-1', public_head='MicroCFTA.SourceCurrentWarmNextPacket.node_call',
    diagnostic_settings_after_checked_module_only=True, proof_declaration_limits_unchanged=True,
    exact_directive_line_matching=True, all_private_type_markers_checked=True,
    actual_axiom_policy='subset of propext, Classical.choice, Quot.sound')
(HERE / 'root-full-preparation-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
