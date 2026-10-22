import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
expected_sha, expected_lines, review_name, expected_review_sha = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
name = 'SourceCurrentOriginalRowClusterCompletion'
source = (here / 'source-proposal' / (name + '.lean')).read_bytes()
assert sha(source) == expected_sha and len(source.splitlines()) == int(expected_lines) <= 350
package = here / 'source-proposal'
for path, pin in json.loads((package / 'pins.json').read_text()).items():
    data = (package / path).read_bytes()
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes'], path
index = json.loads((package / 'source-index.json').read_text())
assert len(index) == 15 and sum(len(item['ranges']) for item in index) == 27
for item in index:
    data = (package / item['snapshot']).read_bytes()
    assert sha(data) == item['sha256'] and Path(item['source']).read_bytes() == data
    for cut in item['ranges']:
        assert (package / cut['snapshot']).read_bytes() == b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
assert (here / 'root-signature-review.json').is_file()
context = (here / 'signature-plan/context.lean.txt').read_bytes()
assert source.startswith(context)
for item in ['private-prefix-signature.lean.txt', 'private-scan-signature.lean.txt', 'proposed-signature.lean.txt']:
    header = (here / 'signature-plan' / item).read_bytes().rstrip(b'\n') + b' := by\n'
    assert source.count(header) == 1, item
text = source.decode()
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert not re.search(r'(?m)^\s*(?:set_option|axiom|opaque|unsafe)\b|\bsorry\b|\badmit\b', text)
assert re.findall(r'(?m)^(?:private )?theorem (\w+)', text) == ['execute_yielded_add', 'scan_boundary_complete', 'cluster_complete']
assert not re.search(r'(?m)^(?:private )?(?:noncomputable )?(?:def|abbrev|instance|structure|inductive|lemma)\b', text)
review = here / review_name
assert review.is_file() and sha(review.read_bytes()) == expected_review_sha
output = here / 'root-source-precheck.json'
assert not output.exists()
result = dict(status='ROOT_ACCEPTED_FOR_ONE_STRICT_CHECK_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=expected_sha, source_lines=int(expected_lines),
    root_read_complete_actual_source=True, independent_whole_source_review=review_name,
    independent_review_sha256=expected_review_sha,
    exact_context_public_header_and_both_helpers_unchanged=True,
    same_source_models_populated_state_global_trace_and_initial_reservation=True,
    genuine_cluster_completion_membership_length_and_all_current_outputs=True,
    future_success_callback_post_room_or_result_law_premise=False,
    default_declaration_limits_and_all_linters_required=True,
    full_output_and_official_install_authorized=False,
    haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'precheck_gate_sha256': sha(output.read_bytes())}))
