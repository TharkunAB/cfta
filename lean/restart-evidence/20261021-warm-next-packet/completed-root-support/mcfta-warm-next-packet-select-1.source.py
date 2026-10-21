import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
author = Path('/tmp/mcfta-warm-next-packet-author')
name = 'SourceCurrentWarmNextPacket.lean'
source = (author / name).read_bytes()
assert hashlib.sha256(source).hexdigest() == '13e8373cff925aca8832a47e12514767dd94dbe3fdb8d68bd73b2cdf19246be8'
assert len(source.splitlines()) == 117
signature = (author / 'proposed-signature.lean.txt').read_bytes()
assert source[source.index(b'theorem node_call\n'):source.index(b'\n := by\n')] + b'\n' == signature
assert source.startswith((author / 'proposed-context.lean.txt').read_bytes())
assert not (ROOT / 'lean/MicroCFTA' / name).exists()
assert not (HERE / name).exists()
(HERE / name).write_bytes(source)
(HERE / 'author-final-freeze.json').write_bytes((author / 'AUTHOR-SOURCE-FROZEN.json').read_bytes())
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=hashlib.sha256(source).hexdigest(), source_lines=117,
    whole_source_root_review='CLEAR', independent_whole_source_review='CLEAR',
    independent_report='/tmp/mcfta-warm-next-packet-source-audit/review.md',
    exact_reviewed_public_header=True, exact_reviewed_context=True,
    one_actual_return_witness=True, reverse_running_both_idles=True,
    ordinary_strict_check_authorized=True, full_check_authorized=False,
    official_edits_authorized=False, declaration_limits_unchanged=True)
(HERE / 'root-source-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
