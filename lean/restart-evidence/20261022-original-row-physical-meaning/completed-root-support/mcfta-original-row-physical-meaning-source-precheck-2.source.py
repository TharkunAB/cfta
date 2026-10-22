import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-physical-meaning')
component, expected_sha, expected_lines, review_name, expected_review_sha, gate_name = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
name = 'SourceCurrentOriginalRowPhysicalMeaning'
package = here / component
source = (package / (name + '.lean')).read_bytes()
assert sha(source) == expected_sha and 0 < len(source.splitlines()) == int(expected_lines) <= 180
for pin in json.loads((package / 'pins.json').read_text()):
    path = pin['path']
    data = (package / path).read_bytes()
    assert sha(data) == pin['sha256'], path
    if 'bytes' in pin:
        assert len(data) == pin['bytes'], path
index = json.loads((package / 'source-index.json').read_text())
assert len(index) == 14 and sum(len(item['ranges']) for item in index) == 21
for item in index:
    data = (here.parents[2] / item['path']).read_bytes()
    assert sha(data) == item['source_sha256'] and data == (package / item['snapshot']).read_bytes()
    for cut in item['ranges']:
        excerpt = b''.join(data.splitlines(True)[cut['start'] - 1:cut['end']])
        assert sha(excerpt) == cut['sha256'] and excerpt == (package / cut['snapshot']).read_bytes()
gate = json.loads((here / 'root-signature-review.json').read_text())
assert gate['status'] == 'ROOT_ACCEPTED_FOR_BODY_PROPOSAL_ONLY'
context = (here / 'signature-plan/context.lean.txt').read_bytes()
assert source.startswith(context)
private = b'private theorem original_of_readback' in source
headers = (['private-signature.lean.txt'] if private else []) + ['proposed-signature.lean.txt']
for item in ['context.lean.txt', *headers]:
    declaration = (here / 'signature-plan' / item).read_bytes()
    assert sha(declaration) == gate['contracts'][item]['sha256']
    if item != 'context.lean.txt':
        assert source.count(declaration.rstrip(b'\n') + b' := by\n') == 1, item
text = source.decode()
assert source.rstrip().endswith(('end MicroCFTA.' + name).encode())
assert not re.search(r'(?m)^\s*(?:set_option|axiom|opaque|unsafe)\b|\bsorry\b|\badmit\b', text)
assert re.findall(r'(?m)^(?:private )?(?:noncomputable )?(?:def|theorem|lemma|abbrev|opaque|structure|inductive|instance) (\w+)', text) == (['original_of_readback'] if private else []) + ['row_inputs_meaning']
review = here / review_name
assert sha(review.read_bytes()) == expected_review_sha
output = here / gate_name
assert not output.exists()
result = dict(status='ROOT_ACCEPTED_FOR_ONE_STRICT_CHECK_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_component=component, source_sha256=expected_sha, source_lines=int(expected_lines),
    root_read_complete_actual_source=True, independent_whole_source_review=review_name,
    independent_review_sha256=expected_review_sha,
    exact_approved_context_and_declaration_headers=True,
    optional_private_codec_helper_present=private,
    same_source_facts_holds_and_admitted_input_model=True,
    literal_row_membership_before_complete_codec_and_payload_readback=True,
    original_and_admitted_children_and_all_ambient_physical_row_equality=True,
    canonical_model_replacement=False, mu_body_closedness_inferred=False,
    success_or_desired_language_premise=False,
    default_declaration_limits_and_all_linters_required=True,
    full_output_and_official_install_authorized=False,
    haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(status='PASS', gate=gate_name, sha256=sha(output.read_bytes()))))
