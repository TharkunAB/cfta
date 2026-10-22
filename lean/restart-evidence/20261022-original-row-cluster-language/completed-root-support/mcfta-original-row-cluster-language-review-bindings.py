import ast
import datetime
import hashlib
import json
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-language')
review_name, review_sha = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
assert sha((here / review_name).read_bytes()) == review_sha
assert sha((here / 'actual-bindings.json').read_bytes()) == '59b271a01a5a1c1f28b185db4ad246978dcd6ab59e645cd26b1a48292b1f9e52'
binding = json.loads((here / 'actual-bindings.json').read_text())
assert len(binding['bindings']) == 9
assertions = 0
for name, pin in binding['bindings'].items():
    template, bound = (here / pin['template']).read_bytes(), (here / name).read_bytes()
    assert sha(template) == pin['template_sha256'] and sha(bound) == pin['bound_sha256']
    before = sum(isinstance(x, ast.Assert) for x in ast.walk(ast.parse(template)))
    after = sum(isinstance(x, ast.Assert) for x in ast.walk(ast.parse(bound)))
    assert before == after
    assertions += after
lines = {name: len((here / name).read_bytes().splitlines()) for name in binding['bindings']}
assert sum(lines.values()) == 758 and assertions == 242
assert binding['contract_insertion_order_preserved']
contracts = json.loads((here / 'actual-approved-contracts.json').read_text())
assert list(contracts) == ['context.lean.txt', 'private-execute-yielded-add.lean.txt',
    'private-scan-boundary-complete.lean.txt', 'proposed-signature.lean.txt',
    'local-complete-statement.lean.txt', 'local-rows-binding.lean.txt', 'local-strong-IH-expanded.lean.txt']
failures = []
for path in sorted(Path('/tmp').glob('mcfta-original-row-cluster-language-*.json')):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and 'wrapper' in item and item.get('exit_code', 0) != 0:
        failures.append(dict(path=str(path), sha256=sha(path.read_bytes()), exit_code=item['exit_code']))
assert len(failures) == 1 and Path(failures[0]['path']).name == 'mcfta-original-row-cluster-language-activate-full-1.json'
gate = dict(status='ROOT_ACCEPTED_FOR_SAVED_METADATA_WORKFLOW',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    tools=binding['bindings'], root_read_all_nine_complete_actual_tools=True,
    total_bound_tool_lines=758, retained_assertions=assertions, actual_line_counts=lines,
    independent_review=review_name, independent_review_sha256=review_sha,
    exact_templates_and_json_safe_bindings_reviewed=True, all_assertions_retained=True,
    actual_job_history_and_all_math_variants_with_exact_warning_repair_retained=True,
    ordered_approved_contracts_checked=True, root_metadata_failures_before_this_gate=failures,
    stopped_activation_distinct_from_warned_Lean_job_and_no_FULL_attempt=True,
    full_H15_edge_law_and_same_actual_middle_packet_retained=True,
    H19_sound_projection_used_for_deletion=True, all_ambient_union_and_full_global_trace_scope_retained=True,
    local_publication_only=True, network_publication='PENDING_USER_APPROVAL',
    earlier_directly_approved_twelve_commits_pushed=True,
    no_additional_lean_jobs_authorized=True, whole_goal_complete=False)
assert not (here / 'root-tool-binding-review.json').exists()
(here / 'root-tool-binding-review.json').write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(dict(status='PASS', tools=9, complete_lines=758, assertions=assertions,
    retained_root_metadata_failures=len(failures))))
