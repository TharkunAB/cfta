import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
prep = HERE / 'full-preparation'
source = (HERE / 'SourceCurrentColdFiniteWarmCalls.lean').read_bytes()
printer = (prep / 'cold-finite-calls-full-printer.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == '3299d48ee9c5ba1d09cbc25c88946b0b67ecc86ac028df67b30eadae8ae40a9d'
assert hashlib.sha256(printer).hexdigest() == 'c15b5496804e405b5cd740f862540ec4754388762ddbd0b1c4d1afc33f99ec33'
assert printer.startswith(source) and len(printer.splitlines()) == 167
assert source == (HERE / 'cold-finite-calls-strict-1.source.lean').read_bytes()
assert json.loads((HERE / 'cold-finite-calls-strict-1.json').read_text())['exit_code'] == 0
assert (HERE / 'cold-finite-calls-strict-1.log').read_bytes() == b''
report = HERE / 'full-preparation-audit/review.md'
assert hashlib.sha256(report.read_bytes()).hexdigest() == '168ceedca74da6ecc780de851f821b6bd0b1195eedeec280a9d9aad19eacda48'
assert not (HERE / 'cold-finite-calls-public-1.json').exists()
pins = {
    'cold-finite-calls-check-full-public.py': '53dc253311d538f01678ceb6623f5397fa1f84c2d8919dcaac69e0f058166183',
    'read-full.py': 'cc80826b1704d5e624f77a2e82fe3627258df4b427dd38b6b08db940ae4847cd',
    'verify-preservation.py': '1c35b398b09c6905870a0715906bf526756de465000da923cfc2c71d1c936b25',
}
for name, pin in pins.items():
    data = (prep / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin and not (HERE / name).exists()
    (HERE / name).write_bytes(data)
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    complete_printer_and_helpers_root_review='CLEAR', independent_whole_preparation_review='CLEAR',
    source_sha256=hashlib.sha256(source).hexdigest(), printer_sha256=hashlib.sha256(printer).hexdigest(),
    activated_helper_pins=pins, sole_full_authorized=True, selected_job='cold-finite-calls-public-1',
    public_head='MicroCFTA.SourceCurrentColdFiniteWarmCalls.constructed_node_calls',
    diagnostic_settings_after_checked_module_only=True, proof_declaration_limits_unchanged=True,
    public_formula_instance_occurrences_required=2, all_private_type_markers_checked=True,
    accepted_TYPE_requires_literal_byte_identity=True,
    actual_axiom_policy='subset of propext, Classical.choice, Quot.sound')
(HERE / 'root-full-preparation-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
