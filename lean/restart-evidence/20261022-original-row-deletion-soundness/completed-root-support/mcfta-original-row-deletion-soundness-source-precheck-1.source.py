import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-deletion-soundness')
component, expected_sha, expected_lines, review_name, expected_review_sha, gate_name = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
name = 'SourceCurrentOriginalRowDeletionSoundness'
package = here / component
source = (package / (name + '.lean')).read_bytes()
assert sha(source) == expected_sha and 0 < len(source.splitlines()) == int(expected_lines) <= 180
pins = json.loads((package / 'pins.json').read_text())
assert isinstance(pins, list)
for pin in pins:
    data = (package / pin['path']).read_bytes()
    assert sha(data) == pin['sha256'], pin['path']
    if 'bytes' in pin:
        assert len(data) == pin['bytes'], pin['path']
index = json.loads((package / 'source-index.json').read_text())
assert index
for item in index:
    data = (here.parents[2] / item['path']).read_bytes()
    assert sha(data) == item['source_sha256'] and data == (package / item['snapshot']).read_bytes()
    for cut in item['ranges']:
        excerpt = b''.join(data.splitlines(True)[cut['start'] - 1:cut['end']])
        assert sha(excerpt) == cut['sha256'] and excerpt == (package / cut['snapshot']).read_bytes()
gate = json.loads((here / 'root-signature-review.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED_FOR_BODY_PROPOSAL_ONLY' and gate['private_helpers_allowed'] == []
for filename in ['context.lean.txt', 'proposed-signature.lean.txt']:
    declaration = (here / 'signature-plan' / filename).read_bytes()
    assert sha(declaration) == gate['contracts'][filename]['sha256']
    if filename == 'context.lean.txt':
        assert source.startswith(declaration)
    else:
        assert source.count(declaration.rstrip(b'\n') + b' := by\n') == 1
text = source.decode()
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert not re.search(r'(?m)^\s*(?:set_option|axiom|opaque|unsafe)\b|\bsorry\b|\badmit\b', text)
assert re.findall(r'(?m)^(?:private )?(?:noncomputable )?(?:def|theorem|lemma|abbrev|opaque|structure|inductive|instance) (\w+)', text) == ['deletion_sound']
review = here / review_name
assert sha(review.read_bytes()) == expected_review_sha
output = here / gate_name
assert not output.exists()
result = dict(status='ROOT_ACCEPTED_FOR_ONE_STRICT_CHECK_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_component=component, source_sha256=expected_sha, source_lines=int(expected_lines),
    root_read_complete_actual_source=True, independent_whole_source_review=review_name,
    independent_review_sha256=expected_review_sha,
    exact_approved_context_and_declaration_headers=True, private_helpers_present=False,
    same_source_facts_holds_admitted_model_and_ranked_input=True,
    two_literal_original_rows_and_same_model_parent_admission_explicit=True,
    full_existing_edge_law_contains_sound_and_complete=True, only_sound_projection_used=True,
    bounded_completeness_projection_used=False, rank_erasure_used=False,
    source_residency_grows_to_exact_final_coherent_heap=True,
    identity_to_complete_payload_equality_derived=True, both_all_ambient_physical_inclusions=True,
    canonical_model_replacement=False, mu_body_closedness_inferred=False,
    new_execution_or_scan_language_claim=False, new_completeness_or_desired_inclusion_oracle=False,
    default_declaration_limits_and_all_linters_required=True,
    full_output_and_official_install_authorized=False,
    haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(status='PASS', gate=gate_name, sha256=sha(output.read_bytes()))))
