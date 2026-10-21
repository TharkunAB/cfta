import datetime
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
report = Path(sys.argv[1]).resolve()
assert report.parent == HERE / 'explicit-instance-audit' and report.is_file()
target = HERE / 'SourceCurrentColdFiniteWarmCalls.lean'
old = target.read_bytes()
assert hashlib.sha256(old).hexdigest() == '3299d48ee9c5ba1d09cbc25c88946b0b67ecc86ac028df67b30eadae8ae40a9d'
assert old == (HERE / 'cold-finite-calls-strict-1.source.lean').read_bytes()
source = (HERE / 'explicit-instance-repair/SourceCurrentColdFiniteWarmCalls.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
assert len(source.splitlines()) == 157
header = source[source.index(b'theorem constructed_node_calls\n'):source.index(b'\n := by\n')] + b'\n'
assert hashlib.sha256(header).hexdigest() == 'a737a2de1dd2bac42ded83643c3bd0f1ba0d71342c1dcdcb75d54111c0020c6a'
assert source.startswith((HERE / 'author/selected-context.lean.txt').read_bytes())
assert not (HERE.parents[2] / 'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean').exists()
target.write_bytes(source)
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=hashlib.sha256(source).hexdigest(), source_lines=157,
    header_sha256=hashlib.sha256(header).hexdigest(), header_lines=32,
    root_whole_source_and_four_explicit_arguments='CLEAR', independent_whole_review='CLEAR',
    independent_report_sha256=hashlib.sha256(report.read_bytes()).hexdigest(),
    mathematical_premises_and_conclusion_retained=True, rejected_FULL1_retained=True,
    ordinary_strict2_authorized=True, new_FULL_requires_clean_strict_and_separate_review=True,
    reader_privacy_conditions_unchanged=True, official_edits_authorized=False)
(HERE / 'root-explicit-instance-repair-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
