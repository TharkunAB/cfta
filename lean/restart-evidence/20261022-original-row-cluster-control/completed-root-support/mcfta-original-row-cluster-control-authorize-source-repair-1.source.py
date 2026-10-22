import datetime
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
before = (HERE / 'original-row-cluster-control-strict-1.source.lean').read_bytes()
source = (HERE / 'source-repair-v2/SourceCurrentOriginalRowClusterScan.lean').read_bytes()
assert sha(before) == '6cd3754ccc6aa63de84b9b56f14d5543dc5e0c8003acf32bd39a074630e4d63a'
assert before.count(b'PairOutcome.done') == 2
assert source == before.replace(b'PairOutcome.done', b'SourceCurrentSameSymbolEdgeControl.Outcome.done')
assert sha(source) == '37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7'
assert len(source.splitlines()) == 129 <= 220
header = (HERE / 'source-repair-v2/proposed-signature.lean.txt').read_bytes()
assert len(header.splitlines()) == 19 and sha(header) == '4356ce96e7673aef7b6598614ae0bc1bdf181f1794b4afeea31a0417e6fb1f85'
assert source.count(header.rstrip(b'\n') + b' := by\n') == 1
failed = json.loads((HERE / 'original-row-cluster-control-strict-1.json').read_text())
raw = (HERE / 'original-row-cluster-control-strict-1.log').read_bytes()
assert failed['exit_code'] == 1 and raw.count(b'error(lean.unknownIdentifier)') == 2 and b'warning' not in raw
review = (HERE / 'source-repair-audit-v2/review.md').read_bytes()
assert sha(review) == sys.argv[1]
target = HERE / 'root-source-repair-authorization.json'
assert not target.exists()
result = dict(status='ROOT_APPROVED_FOR_ONE_STRICT_SOURCE_CHECK',
    source_sha256=sha(source), source_lines=129, public_header_sha256=sha(header),
    root_read_complete_amended_source_and_header=True,
    root_read_complete_independent_review=True, independent_review_sha256=sha(review),
    original_failed_source_and_two_errors_retained=True, only_two_constructor_references_changed=True,
    default_declaration_limits=True, authorized_job='original-row-cluster-control-strict-2',
    compiler_authorized=True, full_public_job_authorized=False,
    genuine_packet_cluster_completion_claimed=False,
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
target.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
