import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
report = json.loads((HERE / 'warm-full-readback.json').read_text())
raw = (HERE / 'warm-packet-public-1.log').read_bytes()
public = (HERE / 'warm-node_call-public-type.txt').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '68cd5d5bf82cfb8fa7d0d1877c5ec78bcd9fff18052735354ba6a61ec6cbfc48'
assert len(raw) == 717427
assert hashlib.sha256(public).hexdigest() == 'ba9168135da3874843326c5381302e4b3c66af99941be3991b33ff174b48e119'
assert len(public.splitlines()) == 518
assert set(report['heads'][0]['actual_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=report['source_sha256'], printer_sha256=report['printer_sha256'],
    raw_log_sha256=hashlib.sha256(raw).hexdigest(), raw_log_bytes=len(raw),
    public_type_sha256=hashlib.sha256(public).hexdigest(), public_type_logical_lines=518,
    root_complete_read_ranges=[[1,190],[191,370],[371,518]],
    complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    independent_report='/tmp/mcfta-warm-next-packet-full-type-audit/review.md',
    whole_check_print_type_identity=True, public_type_private_markers_absent=True,
    actual_axioms=report['heads'][0]['actual_axioms'],
    full_proof_body_preserved_and_programmatically_checked=True,
    full_proof_body_manually_read=False, declaration_limits_unchanged=True,
    official_install_authorized=True, sole_full_jobs=1)
(HERE / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
