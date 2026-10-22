import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
review_name, expected_review_sha = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
name = 'SourceCurrentOriginalRowClusterCompletion'
package = here / 'source-repair-v3'
source = (package / (name + '.lean')).read_bytes()
expected_sha = 'c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b'
assert sha(source) == expected_sha and len(source.splitlines()) == 345 <= 350
for path, pin in json.loads((package / 'pins.json').read_text()).items():
    data = (package / path).read_bytes()
    assert sha(data) == pin['sha256'], path
    if 'bytes' in pin:
        assert len(data) == pin['bytes'], path
context = (package / 'context.lean.txt').read_bytes()
assert sha(context) == 'b33ff6c3d1d1a727389ef150fbde8516e9d622c43901e900a7a08d82658c9f3a'
assert len(context.splitlines()) == 17 and source.startswith(context)
assert context == (here / 'source-repair-v2/context.lean.txt').read_bytes()
original = (here / 'original-row-cluster-completion-strict-2.source.lean').read_bytes()
assert sha(original) == '467e909e1d5c76e2c9cd88c3fa71620635ad3585bb29dbe813825c74f6ecb9c5'
expected = original
for before, after in [
    (b'simpa only [notDropped, promoted, \xe2\x86\x93reduceIte] using prefixRun',
     b'simpa only [ite_eq_right notDropped, ite_eq_left promoted] using prefixRun'),
    (b'            \xc2\xb7 simp only [List.length_reverse, List.length_nil, Nat.zero_add]\n',
     b'            \xc2\xb7 simp only [List.length_reverse, List.length_nil, Nat.zero_add]\n              exact Nat.le_refl _\n')]:
    assert expected.count(before) == 1
    expected = expected.replace(before, after, 1)
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
output = here / 'root-source-precheck-v3.json'
assert not output.exists()
result = dict(status='ROOT_ACCEPTED_FOR_ONE_STRICT_CHECK_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=expected_sha, source_lines=345, context_sha256=sha(context), context_lines=17,
    original_failed_source_sha256=sha(original),
    root_read_complete_actual_source_and_exact_two_site_repair=True,
    independent_whole_source_review=review_name, independent_review_sha256=expected_review_sha,
    exact_public_header_both_helpers_and_context_unchanged=True,
    only_ite_reduction_and_reflexivity_sites_changed=True,
    intended_genuine_cluster_statement_and_state_correlations_unchanged=True,
    default_declaration_limits_and_all_linters_required=True,
    full_output_and_official_install_authorized=False,
    haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'precheck_gate_sha256': sha(output.read_bytes())}))
