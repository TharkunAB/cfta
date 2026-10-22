import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
expected_sha, review_name, expected_review_sha = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
name = 'SourceCurrentOriginalRowClusterCompletion'
package = here / 'source-repair-v2'
source = (package / (name + '.lean')).read_bytes()
assert sha(source) == expected_sha and len(source.splitlines()) == 344 <= 350
for path, pin in json.loads((package / 'pins.json').read_text()).items():
    data = (package / path).read_bytes()
    assert sha(data) == pin['sha256'], path
    if 'bytes' in pin:
        assert len(data) == pin['bytes'], path
context = (package / 'context.lean.txt').read_bytes()
original_context = (here / 'signature-plan/context.lean.txt').read_bytes()
assert len(context.splitlines()) == 17 and context.count(b' InternedEdgeResidency') == 1
assert context.replace(b' InternedEdgeResidency', b'', 1) == original_context
assert source.startswith(context)
original = (here / ('original-row-cluster-completion-strict-1.source.lean')).read_bytes()
assert sha(original) == 'aa72ddb54eeb5a06123af80983c269e5c8aef1bded4f446e65de99fa80e69ec0'
expected = context + original[len(original_context):]
for before, after, count in [(b'have prefix :', b'have prefixRun :', 2),
    (b'using prefix', b'using prefixRun', 3), (b'_ _ _ _ prefix]', b'_ _ _ _ prefixRun]', 1)]:
    assert expected.count(before) == count
    expected = expected.replace(before, after)
assert source == expected
for item in ['private-prefix-signature.lean.txt', 'private-scan-signature.lean.txt', 'proposed-signature.lean.txt']:
    header = (here / 'signature-plan' / item).read_bytes().rstrip(b'\n') + b' := by\n'
    assert source.count(header) == 1, item
text = source.decode()
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert not re.search(r'(?m)^\s*(?:set_option|axiom|opaque|unsafe)\b|\bsorry\b|\badmit\b', text)
assert re.findall(r'(?m)^(?:private )?theorem (\w+)', text) == ['execute_yielded_add', 'scan_boundary_complete', 'cluster_complete']
review = here / review_name
assert sha(review.read_bytes()) == expected_review_sha
output = here / 'root-source-precheck-v2.json'
assert not output.exists()
result = dict(status='ROOT_ACCEPTED_FOR_ONE_STRICT_CHECK_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=expected_sha, source_lines=344, context_sha256=sha(context), context_lines=17,
    original_context_sha256=sha(original_context), original_failed_source_sha256=sha(original),
    root_read_complete_actual_source_and_exact_context_repair=True,
    independent_whole_source_review=review_name, independent_review_sha256=expected_review_sha,
    exact_public_header_and_both_helper_texts_unchanged=True,
    only_namespace_and_six_local_identifier_occurrences_changed=True,
    intended_genuine_cluster_statement_and_state_correlations_unchanged=True,
    default_declaration_limits_and_all_linters_required=True,
    full_output_and_official_install_authorized=False,
    haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'precheck_gate_sha256': sha(output.read_bytes())}))
