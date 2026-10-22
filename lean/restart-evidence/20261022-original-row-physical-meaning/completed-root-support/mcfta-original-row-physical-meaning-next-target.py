import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-physical-meaning'
def sha(data):
    return hashlib.sha256(data).hexdigest()
plan = here / 'next-deletion-plan'
for pin in json.loads((plan / 'pins.json').read_text()):
    data = (plan / pin['path']).read_bytes()
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes']
index = json.loads((plan / 'source-index.json').read_text())
assert len(index) == 12 and sum(len(item['ranges']) for item in index) == 17
for item in index:
    path = root / item['path'] if item['root_relative'] else Path(item['path'])
    data = path.read_bytes()
    assert sha(data) == item['source_sha256']
    for cut in item['ranges']:
        excerpt = b''.join(data.splitlines(True)[cut['start'] - 1:cut['end']])
        assert sha(excerpt) == cut['sha256'] and excerpt == (plan / cut['snapshot']).read_bytes()
selected = here / 'next-deletion-plan-erratum/selected-proposed-contract.md'
assert sha(selected.read_bytes()) == 'dae140afdb1c7b836d3232d41722db0dbf90da756bc00d16ba253107c2ea4775'
review = here / 'next-deletion-plan-audit/review.md'
assert sha(review.read_bytes()) == '3b1fc36ec70d86d857e4111358a2749019f9805be55b1be48dff30885b7f3ca3'
assert json.loads((here / 'original-row-physical-meaning-audit-1.json').read_text())['exit_code'] == 0
assert (root / 'lean/MicroCFTA/SourceCurrentOriginalRowPhysicalMeaning.lean').read_bytes() == (here / 'SourceCurrentOriginalRowPhysicalMeaning.lean').read_bytes()
gate = dict(status='ROOT_ACCEPTED_FOR_FRESH_BASELINE_AND_EXACT_DECLARATION_PROPOSAL_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    target='SourceCurrentOriginalRowDeletionSoundness.deletion_sound',
    selected_contract=str(selected.relative_to(here)), selected_contract_sha256=sha(selected.read_bytes()),
    independent_review=str(review.relative_to(here)), independent_review_sha256=sha(review.read_bytes()),
    root_read_all_notes_selected_contract_and_17_api_cuts=True,
    source_count=12, exact_cuts=17, target_lines=[90, 140], hard_stop_lines=180,
    one_public_theorem=True, optional_private_helper='canonical_sound',
    same_admitted_model_and_same_completed_h15_result=True,
    only_edge_law_sound_projection_needed=True, identity_to_complete_payload_equality_derived=True,
    candidate_test_first=True, canonical_conjunction_swap_only=True,
    future_cluster_retains_genuine_h17_width_and_global_room=True,
    completed_comparison_or_total_exact_meet_oracle=False,
    body_or_compiler_or_official_install_authorized=False,
    scan_language_preservation_claimed=False, haskell_changes=False, whole_goal_complete=False)
assert not (here / 'next-deletion-root-review.json').exists() and not (here / 'NEXT-TARGET.md').exists()
(here / 'next-deletion-root-review.json').write_text(json.dumps(gate, indent=2) + '\n')
(here / 'NEXT-TARGET.md').write_text('''# Next: sound identity-based deletion

H18 row_inputs_meaning passes clean strict1, sole FULL1 and Audit1.
Its exact original/admitted child and all-ambient physical row conclusions are checked.
H6 constructed_node_calls remains the strongest combined semantic theorem.

Read next-deletion-plan/note.md, proof-route.md and remaining-obligations.md.
Use next-deletion-plan-erratum/selected-proposed-contract.md in place of the original contract.
Root and independent review have read the selected scope and all 17 API cuts.
The original uncompiled-H18 cue remains a historical observation.

First refresh upstream and make a fresh preserving baseline and backup.
Then propose exact context, one public deletion_sound statement and at most
one private canonical_sound statement in SourceCurrentOriginalRowDeletionSoundness.
Only these declarations are authorized next. No body or compiler run is authorized yet.
Use 90 to 140 ordinary total source lines, with a hard stop at 180.
Keep default declaration limits and all linters.

Keep one fixed source Facts, arbitrary holds, admitted inputModel, ranked input,
available closed original parent and two literal rows from that parent.
Keep the actual H15 common edge, final coherent heap, source-to-final growth,
result residency and canonical empty-domain EdgeLaw as completed-past arguments.
Use H18 for the two child packets and physical row languages.
Use only EdgeLaw.sound and sound_empty_domain. Preserve the fixed ranked index.
Use source row residency, growth and edge_identity_unique to derive complete
row equality from each tested identity equality in the exact final heap.
Common=candidate must imply candidate language included in pivot language.
Common=pivot must imply pivot language included in candidate language.
Keep candidate-first control. Canonical ordering swaps only the semantic conjunction.

Compose the adapter with the SAME H15 witness at the existing scan call site.
Retain the currently discarded resident/law and every other current packet field.
No new comparison run, reset, total exact meet, rank erasure or native Receipt is needed.
Parent model admission is explicit. H17 does not currently require it.
The later cluster semantic theorem must retain genuine H17 width and global Room.
The adapter itself needs no operational success, width or Room premise.

The scan union-language invariant and physical pruning theorem remain open.
Then handle grouping, reconstruction, generated parents and recursive/Mu traversal.
The full public pass, practical width, solver composition, convergence and Haskell
correspondence remain open. The whole goal stays active.
Do not edit H18 after sealing. Keep FINDINGS external Haskell repair index first.
Remote publication still needs the pending fresh approval after automatic review rejection.
''')
print(json.dumps(dict(status='PASS', exact_declarations_only=True, next_target=gate['target'])))
