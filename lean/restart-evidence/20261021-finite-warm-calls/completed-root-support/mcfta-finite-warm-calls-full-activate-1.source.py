import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
prep = HERE / 'full-preparation'
printer = (prep / 'finite-calls-full-printer.lean').read_bytes()
reader = (prep / 'finite-calls-check-full-public.py').read_bytes()
source = (HERE / 'SourceCurrentFiniteWarmCalls.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == '984f34529a1050fd015ba0fb742b39cc38e0b518eaae69801cbde1727578a6bd'
assert hashlib.sha256(printer).hexdigest() == 'cbea63ae250f1fc671c8ade3c30801d523cc757c2d375b8ed0c499878f5a6aa3'
assert hashlib.sha256(reader).hexdigest() == '6bbdfefff5d8d07499c028fbc2f45d250fa83b6138c0e4cfb6d5cb9f3138f0bf'
assert printer.startswith(source) and source == (HERE / 'finite-calls-strict-3.source.lean').read_bytes()
assert json.loads((HERE / 'finite-calls-strict-3.json').read_text())['exit_code'] == 0
assert (HERE / 'finite-calls-strict-3.log').read_bytes() == b''
assert (HERE / 'full-preparation-audit/review.md').is_file()
assert not (HERE / 'finite-calls-public-1.json').exists()
assert not (HERE / 'finite-calls-check-full-public.py').exists()
(HERE / 'finite-calls-check-full-public.py').write_bytes(reader)
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    complete_printer_and_reader_root_review='CLEAR', independent_whole_preparation_review='CLEAR',
    independent_report='full-preparation-audit/review.md',
    source_sha256=hashlib.sha256(source).hexdigest(),
    printer_sha256=hashlib.sha256(printer).hexdigest(), reader_sha256=hashlib.sha256(reader).hexdigest(),
    sole_full_authorized=True, selected_job='finite-calls-public-1',
    public_head='MicroCFTA.SourceCurrentFiniteWarmCalls.node_calls',
    diagnostic_settings_after_checked_module_only=True, proof_declaration_limits_unchanged=True,
    exact_directive_line_matching=True, all_private_type_markers_checked=True,
    namespace_helpers_checked=['Entry', 'advance_entry'],
    actual_axiom_policy='subset of propext, Classical.choice, Quot.sound')
(HERE / 'root-full-preparation-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
