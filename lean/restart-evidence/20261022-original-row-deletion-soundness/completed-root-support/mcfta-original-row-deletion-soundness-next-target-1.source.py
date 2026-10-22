import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-deletion-soundness'
def sha(data):
    return hashlib.sha256(data).hexdigest()
for component in ['next-scan-plan', 'next-scan-plan-erratum']:
    package = here / component
    pins = json.loads((package / 'pins.json').read_text())
    assert isinstance(pins, list)
    for pin in pins:
        data = (package / pin['path']).read_bytes()
        assert sha(data) == pin['sha256'] and len(data) == pin['bytes'], pin['path']
package = here / 'next-scan-plan'
index = json.loads((package / 'source-index.json').read_text())
cuts = 0
for item in index:
    path = Path(item['path'])
    raw = (path if path.is_absolute() else root / path).read_bytes()
    assert sha(raw) == item['source_sha256'] and len(raw) == item['source_bytes']
    if 'snapshot' in item:
        assert raw == (package / item['snapshot']).read_bytes()
    for cut in item['ranges']:
        excerpt = b''.join(raw.splitlines(True)[cut['start'] - 1:cut['end']])
        assert sha(excerpt) == cut['sha256'] and excerpt == (package / cut['snapshot']).read_bytes()
        cuts += 1
assert len(index) == 11 and cuts == 16
assert sha((here / 'next-scan-plan-audit/review.md').read_bytes()) == '5d3be74e4d400f127954bd1e7c3eb0c00d14e4c4c8f21260f3cddc31d860ee06'
source_sha = 'a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a'
assert sha((root / 'lean/MicroCFTA/SourceCurrentOriginalRowDeletionSoundness.lean').read_bytes()) == source_sha
for kind in ['strict', 'public', 'audit']:
    assert json.loads((here / ('original-row-deletion-soundness-' + kind + '-1.json')).read_text())['exit_code'] == 0
assert not (here / 'next-scan-root-review.json').exists() and not (here / 'NEXT-TARGET.md').exists()
review = dict(status='ROOT_ACCEPTED_SOURCE_PLAN_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    root_read_context18_public_sketch57_whole_H17_345_and_all16_api_cuts=True,
    api_sources=11, exact_api_cuts=16, independent_review='next-scan-plan-audit/review.md',
    selected_route='next-scan-plan-erratum/selected-proof-route.md',
    h19_checked_source_sha256=source_sha, strict_full_audit_pass=True,
    same_actual_h15_witness_and_entire_current_packet_required=True,
    fixed_same_admitted_parent_model_and_global_width_room_trace_required=True,
    exact_candidate_first_control_and_promotion_reverse_order_required=True,
    old_checked_modules_must_remain_unchanged=True,
    proposed_target_lines=[410,480], proposed_hard_stop_lines=500,
    fresh_baseline_and_exact_all_declarations_review_required=True,
    new_private_helpers_or_body_or_compiler_authorized=False, whole_goal_complete=False)
(here / 'next-scan-root-review.json').write_text(json.dumps(review, indent=2) + '\n')
(here / 'NEXT-TARGET.md').write_text('''# Next target: original-row cluster language preservation

H19 deletion_sound passes strict1, sole FULL1 and Audit1 at this checkpoint.
Its selected source has105 lines and SHA a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a.
The historical next-scan plan predates those checks. Keep its original wording.
Use next-scan-plan-erratum/selected-proof-route.md and next-scan-plan-audit/review.md.

Start a fresh baseline before proposing the next exact module context and all declarations.
The candidate module is SourceCurrentOriginalRowClusterLanguage.
Retain all H17 execution and packet outputs. Add same-model parent admission and
an all-ambient physical union-language iff between actual kept and original group rows.
Strengthen a new copy of the concrete H17 construction. Keep old modules unchanged.
At its existing comparison call, retain the SAME H15 common edge, result residency,
canonical EdgeLaw, middle state and all current packet fields. Apply H19 once.
Use middle.checked.native.machine.heap, its actual coherence and composed growth.
Keep genuine width, global Room, initial-domain Valid and the SAME final allocation Trace.
Do not add a comparison, future-success premise, post-Room oracle or replacement model.
Use candidate-first deletion, actual promotion and reverse reconstruction order.
Preserve the union language. Do not claim Sublist or semantic incomparability.

The proposed target is410–480 total ordinary lines with proposed hard500.
These estimates do not authorize a body, helper or compiler run.
Review the exact public and private declarations and total budget at the next source gate.
Grouping, reconstruction, generated parents, Mu/full pass, practical width,
solver composition, Haskell refinement and convergence remain open.
H6 remains the strongest combined semantic theorem. The whole goal is incomplete.
''')
print(json.dumps(dict(status='PASS', next_target='cluster_complete_with_language',
    fresh_declaration_gate_only=True, sources=11, cuts=16)))
