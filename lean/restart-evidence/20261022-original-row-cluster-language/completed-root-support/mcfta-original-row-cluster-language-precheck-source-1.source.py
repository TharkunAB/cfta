import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-language')
component, expected_sha, expected_lines, review_name, expected_review_sha, gate_name = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
name = 'SourceCurrentOriginalRowClusterLanguage'
package = here / component
source = (package / (name + '.lean')).read_bytes()
assert sha(source) == expected_sha and 0 < len(source.splitlines()) == int(expected_lines) <= 500
pins = json.loads((package / 'pins.json').read_text())
assert isinstance(pins, (list, dict)) and pins
entries = pins if isinstance(pins, list) else [dict(path=path, **pin) for path, pin in pins.items()]
for pin in entries:
    data = (package / pin['path']).read_bytes()
    assert sha(data) == pin['sha256'], pin['path']
    if 'bytes' in pin:
        assert len(data) == pin['bytes'], pin['path']
index = json.loads((package / 'source-index.json').read_text())
assert isinstance(index, list) and index
for item in index:
    path = Path(item['path'])
    data = (path if path.is_absolute() else here.parents[2] / path).read_bytes()
    assert sha(data) == item['source_sha256'] and data == (package / item['snapshot']).read_bytes()
    for cut in item['ranges']:
        excerpt = b''.join(data.splitlines(True)[cut['start'] - 1:cut['end']])
        assert sha(excerpt) == cut['sha256'] and excerpt == (package / cut['snapshot']).read_bytes()
gate = json.loads((here / 'root-signature-review.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED_FOR_BODY_PROPOSAL_ONLY'
assert gate['private_helpers_allowed'] == ['execute_yielded_add', 'scan_boundary_complete']
headers = ['context.lean.txt', 'private-execute-yielded-add.lean.txt',
    'private-scan-boundary-complete.lean.txt', 'proposed-signature.lean.txt',
    'local-complete-statement.lean.txt']
positions = []
for filename in headers:
    declaration = (here / 'signature-plan' / filename).read_bytes()
    assert sha(declaration) == gate['contracts'][filename]['sha256']
    if filename == 'context.lean.txt':
        assert source.startswith(declaration)
        positions.append(0)
    else:
        fragment = declaration.rstrip(b'\n') + b' := by\n'
        assert source.count(fragment) == 1, filename
        positions.append(source.index(fragment))
assert positions == sorted(positions)
rows = (here / 'signature-plan/local-rows-binding.lean.txt').read_bytes()
assert source.count(b'\n' + rows) == 1
assert positions[3] < source.index(b'\n' + rows) < positions[4]
expanded = (here / 'signature-plan/local-strong-IH-expanded.lean.txt').read_bytes()
assert expanded not in source
text = source.decode()
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert not re.search(r'(?m)^\s*(?:set_option|axiom|opaque|unsafe)\b|\bsorry\b|\badmit\b', text)
assert re.findall(r'(?m)^(?:private )?(?:noncomputable )?(?:def|theorem|lemma|abbrev|opaque|structure|inductive|instance) (\w+)', text) == [
    'execute_yielded_add', 'scan_boundary_complete', 'cluster_complete']
review = here / review_name
assert sha(review.read_bytes()) == expected_review_sha
output = here / gate_name
assert not output.exists()
result = dict(status='ROOT_ACCEPTED_FOR_ONE_STRICT_CHECK_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_component=component, source_sha256=expected_sha, source_lines=int(expected_lines),
    root_read_complete_actual_source=True, independent_whole_source_review=review_name,
    independent_review_sha256=expected_review_sha,
    exact_approved_context_private_public_local_headers_and_order=True,
    private_helpers_present=['execute_yielded_add', 'scan_boundary_complete'],
    same_source_facts_holds_admitted_model_ranked_input_and_literal_filtered_rows=True,
    same_H15_common_middle_done_resident_full_edge_law_and_packet=True,
    H19_applied_to_same_middle_coherent_heap_and_composed_source_growth=True,
    actual_candidate_first_promotion_and_reversed_accumulator_union_invariant=True,
    all_ambient_finite_term_physical_kept_union_iff_original_symbol_group=True,
    every_old_cache_extension_returned_idle_output_and_global_domain_trace_retained=True,
    genuine_initial_width_Room_and_initial_domain_Valid_remain_required=True,
    new_success_or_desired_language_or_per_comparison_Room_or_generated_parent_oracle=False,
    default_declaration_limits_and_all_linters_required=True,
    full_output_and_official_install_authorized=False,
    haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(status='PASS', gate=gate_name, sha256=sha(output.read_bytes()))))
