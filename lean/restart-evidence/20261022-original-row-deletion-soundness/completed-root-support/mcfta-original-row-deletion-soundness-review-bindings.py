import ast
import datetime
import hashlib
import json
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-deletion-soundness')
review_name, review_sha = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
assert sha((here / review_name).read_bytes()) == review_sha
binding = json.loads((here / 'actual-bindings.json').read_text())
assert len(binding['bindings']) == 9
for name, pin in binding['bindings'].items():
    template, bound = (here / pin['template']).read_bytes(), (here / name).read_bytes()
    assert sha(template) == pin['template_sha256'] and sha(bound) == pin['bound_sha256']
    assert sum(isinstance(x, ast.Assert) for x in ast.walk(ast.parse(template))) == sum(isinstance(x, ast.Assert) for x in ast.walk(ast.parse(bound)))
lines = {name: len((here / name).read_bytes().splitlines()) for name in binding['bindings']}
assert sum(lines.values()) == 752
assert binding['contract_insertion_order_preserved']
contracts = json.loads((here / 'actual-approved-contracts.json').read_text())
assert list(contracts) == ['context.lean.txt', 'proposed-signature.lean.txt']
gate = dict(status='ROOT_ACCEPTED_FOR_SAVED_METADATA_WORKFLOW',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    tools=binding['bindings'], root_read_all_nine_complete_actual_tools=True,
    total_bound_tool_lines=752, actual_line_counts=lines,
    independent_review=review_name, independent_review_sha256=review_sha,
    exact_templates_and_json_safe_bindings_reviewed=True, all_assertions_retained=True,
    actual_failed_and_successful_job_history_retained=True,
    ordered_approved_contracts_checked=True, no_root_metadata_failure_before_this_gate=True,
    explicit_full_edge_law_sound_and_complete_scope_retained=True,
    only_sound_projection_used=True, local_publication_only=True,
    network_publication='PENDING_USER_APPROVAL',
    no_additional_lean_jobs_authorized=True, whole_goal_complete=False)
assert not (here / 'root-tool-binding-review.json').exists()
(here / 'root-tool-binding-review.json').write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(dict(status='PASS', tools=9, complete_lines=752)))
