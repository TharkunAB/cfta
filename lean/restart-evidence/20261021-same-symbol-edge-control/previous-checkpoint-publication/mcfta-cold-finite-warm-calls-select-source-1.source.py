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
name = 'SourceCurrentColdFiniteWarmCalls.lean'
source = (author / name).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == '3299d48ee9c5ba1d09cbc25c88946b0b67ecc86ac028df67b30eadae8ae40a9d'
assert len(source.splitlines()) == 153
signature = (author / 'extracted-header.lean.txt').read_bytes()
assert hashlib.sha256(signature).hexdigest() == '52c52542dfcba31ddbf5d69e64da9cefcda9288a4e6df3ad7d30217753ed9c27'
assert source[source.index(b'theorem constructed_node_calls\n'):source.index(b'\n := by\n')] + b'\n' == signature
context = (author / 'selected-context.lean.txt').read_bytes()
assert hashlib.sha256(context).hexdigest() == '4add6d71727d9123320e604fc5751ee79091e2675bfba9a9e01139bbc61348fb'
assert source.startswith(context)
assert json.loads((author / 'AUTHOR-SOURCE-FROZEN.json').read_text())['source_sha256'] == sha
assert not (ROOT / 'lean/MicroCFTA' / name).exists() and not (HERE / name).exists()
(HERE / name).write_bytes(source)
review = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=sha, source_lines=153, whole_source_root_review='CLEAR',
    independent_whole_source_review='CLEAR', independent_report=str(report.relative_to(HERE)),
    independent_report_sha256=hashlib.sha256(report.read_bytes()).hexdigest(),
    exact_reviewed_public_header=True, exact_reviewed_public_instance_context=True,
    one_actual_source_construction=True, width_chosen_before_fresh_caller=True,
    one_finite_producer_invocation=True, same_actual_trace_and_final_heap=True,
    empty_inherited_semantic_specialization=True,
    ordinary_strict_check_authorized=True, full_check_authorized=False,
    official_edits_authorized=False, declaration_limits_unchanged=True)
(HERE / 'root-source-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
