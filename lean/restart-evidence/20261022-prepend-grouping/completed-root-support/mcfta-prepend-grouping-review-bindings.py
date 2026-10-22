import ast
import datetime
import hashlib
import json
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-prepend-grouping')
sha = lambda data: hashlib.sha256(data).hexdigest()
review_sha = sys.argv[1]
review_path = 'actual-binding-audit/review.md'
assert sha((here / review_path).read_bytes()) == review_sha
binding_raw = (here / 'actual-bindings.json').read_bytes()
assert sha(binding_raw) == '72e9312532af205aab9f1cc6e7d1e721156f9a4aee69c6aef6563760709bd902'
binding = json.loads(binding_raw)
assert len(binding['bindings']) == 9
lines, assertions = {}, 0
for name, pin in binding['bindings'].items():
    before, after = (here / pin['template']).read_bytes(), (here / name).read_bytes()
    assert sha(before) == pin['template_sha256'] and sha(after) == pin['bound_sha256']
    count = lambda raw: sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(raw)))
    assert count(before) == count(after)
    assertions += count(after)
    lines[name] = len(after.splitlines())
assert sum(lines.values()) == 805 and assertions == 270
failures = []
for path in sorted(Path('/tmp').glob('mcfta-prepend-grouping-*.json')):
    item = json.loads(path.read_text())
    if isinstance(item,dict) and 'wrapper' in item and item.get('exit_code',0) != 0:
        failures.append(dict(path=str(path),sha256=sha(path.read_bytes()),exit_code=item['exit_code']))
assert len(failures) == 1 and Path(failures[0]['path']).name == 'mcfta-prepend-grouping-read-full-1.json'
gate = dict(status='ROOT_ACCEPTED_FOR_SAVED_METADATA_WORKFLOW',observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    tools=binding['bindings'],root_read_all_nine_complete_actual_tools=True,total_bound_tool_lines=805,retained_assertions=270,
    actual_line_counts=lines,independent_review=review_path,independent_review_sha256=review_sha,
    exact_templates_and_json_safe_bindings_reviewed=True,all_assertions_retained=True,actual_source_history_and_three_repairs_retained=True,
    lexical_identity_and_actual_raw_byte_flags_reviewed=True,dual_reader_v3_paths_pinned=True,root_metadata_failures_before_this_gate=failures,
    old_v2_review_hold_erratum_and_repair_retained=True,local_publication_only=True,network_publication='PENDING_USER_APPROVAL',
    earlier_directly_approved_twelve_commits_pushed=True,no_additional_lean_jobs_authorized=True,whole_goal_complete=False)
assert not (here / 'root-tool-binding-review.json').exists()
(here / 'root-tool-binding-review.json').write_text(json.dumps(gate,indent=2) + '\n')
print(json.dumps(dict(status='PASS',tools=9,complete_lines=805,assertions=270,retained_root_metadata_failures=1)))
