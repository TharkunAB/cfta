import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sha = lambda raw: hashlib.sha256(raw).hexdigest()
source = (HERE / 'source-proposal/SourceCurrentOriginalRowClusterScan.lean').read_bytes()
assert sha(source) == '6cd3754ccc6aa63de84b9b56f14d5543dc5e0c8003acf32bd39a074630e4d63a'
assert len(source.splitlines()) == 129 <= 220
for name in ['context.lean.txt', 'proposed-signature.lean.txt', 'declaration-schema.md']:
    assert (HERE / 'source-proposal' / name).read_bytes() == (HERE / 'signature-plan' / name).read_bytes()
context = (HERE / 'signature-plan/context.lean.txt').read_bytes()
header = (HERE / 'signature-plan/proposed-signature.lean.txt').read_bytes().rstrip(b'\n') + b' := by\n'
assert source.startswith(context) and source.count(header) == 1
assert len(context.splitlines()) == 12 and len(header.splitlines()) == 19
assert not re.search(rb'(?m)^\s*(?:private\b|set_option\b|axiom\b|opaque\b)', source)
assert not re.search(rb'\bsorry\b|\badmit\b', source)
declarations = re.findall(rb'(?m)^(?:noncomputable )?(?:inductive|def|theorem) ([A-Za-z_]+)', source)
assert declarations == [b'Control', b'Outcome', b'step', b'execute', b'comparison_lift']
review = (HERE / 'source-audit/review.md').read_bytes()
assert sha(review) == sys.argv[1]
pins = json.loads((HERE / 'source-proposal/pins.json').read_text())['files']
for name, expected in pins.items():
    assert sha((HERE / 'source-proposal' / name).read_bytes()) == expected['sha256']
body_gate = json.loads((HERE / 'source-body-authorization.json').read_text())
assert body_gate['definition_body_authorized'] and body_gate['theorem_body_authorized']
assert not body_gate['compiler_authorized']
target = HERE / 'root-source-authorization.json'
assert not target.exists()
result = dict(status='ROOT_APPROVED_FOR_ONE_STRICT_SOURCE_CHECK',
    source_sha256=sha(source), source_lines=129, context_lines=12, public_header_lines=19,
    actual_header_sha256=sha(header), independent_source_review_sha256=sha(review),
    root_read_complete_source=True, root_read_complete_independent_review=True,
    root_read_complete_context_header_schema_and_relevant_live_h7_haskell_cuts=True,
    default_declaration_limits=True, private_helpers=[],
    compiler_authorized=True, authorized_job='original-row-cluster-control-strict-1',
    full_public_job_authorized=False, official_install_authorized=False,
    conditional_completed_comparison_lift_only=True,
    genuine_packet_cluster_completion_claimed=False, haskell_refinement_claimed=False,
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
target.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
