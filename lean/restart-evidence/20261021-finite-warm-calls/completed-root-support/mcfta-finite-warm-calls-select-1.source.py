import datetime
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
report = Path(sys.argv[1]).resolve()
assert report.parent == HERE / 'source-audit' and report.is_file()
author = HERE / 'author'
name = 'SourceCurrentFiniteWarmCalls.lean'
source = (author / name).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == '32cfa9e1a229237dcaf683fe77f588cb2eeb541929f7e4dff33ef2809370183c'
assert len(source.splitlines()) == 236
signature = (author / 'amended-proposed-signature.lean.txt').read_bytes()
assert source[source.index(b'theorem node_calls\n'):source.index(b'\n := by\n')] + b'\n' == signature
assert source.startswith((author / 'frozen-plan-inputs/proposed-context.lean.txt').read_bytes())
assert json.loads((author / 'AUTHOR-SOURCE-FROZEN.json').read_text())['source_sha256'] == sha
assert not (ROOT / 'lean/MicroCFTA' / name).exists() and not (HERE / name).exists()
(HERE / name).write_bytes(source)
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=sha, source_lines=236, whole_source_root_review='CLEAR',
    independent_whole_source_review='CLEAR', independent_report=str(report.relative_to(HERE)),
    independent_report_sha256=hashlib.sha256(report.read_bytes()).hexdigest(),
    exact_reviewed_public_header=True, exact_reviewed_context=True,
    fixed_global_horizon_width_and_fuels=True, actual_base_and_common_return_same=True,
    exact_next_stage_resources=True, same_final_heap_and_cumulative_node_law=True,
    ordinary_strict_check_authorized=True, full_check_authorized=False,
    official_edits_authorized=False, declaration_limits_unchanged=True)
(HERE / 'root-source-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
