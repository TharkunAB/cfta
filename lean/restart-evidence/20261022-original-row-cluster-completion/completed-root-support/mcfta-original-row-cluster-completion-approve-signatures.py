import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
def sha(data):
    return hashlib.sha256(data).hexdigest()
for component in ['signature-plan', 'signature-audit']:
    package = here / component
    pins = json.loads((package / 'pins.json').read_text())['files']
    for name, pin in pins.items():
        data = (package / name).read_bytes()
        assert sha(data) == pin['sha256'], name
        if 'bytes' in pin:
            assert len(data) == pin['bytes'], name
        if 'splitlines' in pin:
            assert len(data.splitlines()) == pin['splitlines'], name
plan = here / 'signature-plan'
index = json.loads((plan / 'source-index.json').read_text())
assert len(index) == 12 and sum(len(item['ranges']) for item in index) == 21
for item in index:
    data = (plan / item['snapshot']).read_bytes()
    assert sha(data) == item['sha256'] and Path(item['source']).read_bytes() == data
    for cut in item['ranges']:
        assert (plan / cut['snapshot']).read_bytes() == b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
review = here / 'signature-audit/review.md'
assert sha(review.read_bytes()) == 'e319818f9c5c1e745214dcec251aec1e650303f0adb7d96d6f388e1196a54ac3'
observations = json.loads((here / 'signature-audit/observations.json').read_text())
assert observations['status'] == 'EXACT_DECLARATIONS_SOURCE_CLEAR_NOT_ELABORATED'
assert observations['current_genuine_packet_explicit'] and observations['strict_and_total_worker_bounds_sound']
assert not observations['public_future_or_observed_completion_premise']
frozen = json.loads((plan / 'FROZEN.json').read_text())
assert frozen['context_and_header_total_lines'] == 137
for name, expected in frozen['selected_declaration_hashes'].items():
    assert sha((plan / name).read_bytes()) == expected
output = here / 'root-signature-review.json'
assert not output.exists()
result = dict(status='ROOT_APPROVED_FOR_ONE_EXTERNAL_SOURCE_BODY_PROPOSAL_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source='SourceCurrentOriginalRowClusterCompletion.lean', public_theorem='cluster_complete',
    exact_declaration_hashes=frozen['selected_declaration_hashes'],
    independent_review_sha256=sha(review.read_bytes()),
    root_read_whole_context_public_header_and_both_private_headers=True,
    same_source_models_populated_state_initial_domains_and_global_trace=True,
    exact_original_parent_filtered_symbol_group=True,
    actual_cluster_done_and_all_current_invariants_required=True,
    future_success_callback_post_room_or_result_law_premise=False,
    target_source_lines=[270, 350], hard_stop_source_lines=350,
    local_generalized_induction_statement_counts_toward_limit=True,
    allowed_private_helpers=['execute_yielded_add', 'scan_boundary_complete'],
    source_body_proposal_authorized=True, compiler_authorized=False,
    unchanged_default_limits_and_all_linters_required=True,
    complete_source_root_and_independent_review_required_before_check=True,
    physical_pruning_or_haskell_refinement_claimed=False, whole_goal_complete=False)
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'gate_sha256': sha(output.read_bytes())}))
