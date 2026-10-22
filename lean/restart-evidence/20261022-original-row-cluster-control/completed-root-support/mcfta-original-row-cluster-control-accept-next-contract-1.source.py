import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
review = (HERE / 'next-cluster-completion-plan-audit/review.md').read_bytes()
assert hashlib.sha256(review).hexdigest() == sys.argv[1]
plan_pins = (HERE / 'next-cluster-completion-plan/pins.json').read_bytes()
assert hashlib.sha256(plan_pins).hexdigest() == '68ca68ca05a8fafb24500905cf0f2edb3886bdc580ff99f2db0b59b202982781'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40
gate = dict(status='ROOT_APPROVED_FOR_EXACT_CONTEXT_AND_PUBLIC_HEADER_PROPOSAL_ONLY',
    current_proof_commit=proof, current_source_sha256='37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7',
    independent_plan_review_sha256=sys.argv[1], root_read_complete_contract_context_route_and_indexed_cuts=True,
    next_source='SourceCurrentOriginalRowClusterCompletion.lean', next_public_theorem='cluster_complete',
    actual_h16_runner_done_equation_required=True, exact_one_parent_filtered_symbol_group=True,
    same_source_models_initial_domains_reservation_and_global_trace=True,
    same_evolving_full_h7_state=True, original_membership_and_length_bound_required=True,
    all_current_invariants_and_composable_effects_required=True,
    future_success_or_callback_premise=False, ordered_sublist_claim=False,
    helpers=['yielded_prefix_composition', 'actual_scan_boundary_completion'],
    source_target_lines=[270, 350], source_hard_stop_lines=350,
    exact_lean_context_header_and_helper_statements_review='PENDING_NEXT_COMPONENT',
    definition_body_authorized=False, theorem_body_authorized=False, compiler_authorized=False,
    default_declaration_limits_required=True, fresh_upstream_and_baseline_required=True,
    physical_pruning_or_haskell_refinement_claimed=False, whole_goal_complete=False,
    remote_publication='PENDING_USER_APPROVAL')
assert not (HERE / 'next-cluster-root-review.json').exists()
(HERE / 'next-cluster-root-review.json').write_text(json.dumps(gate, indent=2) + '\n')
text = f'''# Next proof target

The checked H16 source is SourceCurrentOriginalRowClusterScan.lean.
Its proof commit is {proof}.
comparison_lift uses an observed completed comparison. It is not a cluster producer.

Continue toward the complete withoutRedundantEdges pass.
Read next-cluster-completion-plan and its independent review.
Prepare the exact context, public cluster_complete header and two helper statements
for SourceCurrentOriginalRowClusterCompletion.lean. This proposal alone is authorized.
Review all exact declarations before authorizing any body or compiler command.

Use one fixed available closed OriginalInput parent and its exact filtered symbol group.
Keep the SAME source/view/model/ranks, populated H7 State, initial domain cache,
Valid witness, global allocation Trace and one initial Room reservation.
Use H15 with the same parent twice to derive every actual comparison.
Conclude an actual H16.execute fuel (.cluster rows []) before = .done kept after.
Retain original-row membership, a length bound, Good, Contextual, SemanticReady,
Stable, native Idle, native Extension, pair-table Extends, Returned and the SAME global Trace.
Derive later source growth/history from the actual Extension. Do not reset a cache or history.
Do not assume future success, a completion callback, new Room or a desired result law.

Use outer strong induction on cluster length and inner induction on remaining scan rows.
The scan worker must yield an actual cluster boundary with strictly smaller active length.
Use H16's positive consumed comparison prefix and a yielded-prefix composition lemma.
Promotion can change order. Prove membership and length, not an ordered Sublist.
Generated common edges must not become later operands.

Review the exact public context and resource-aware helper statements before the body.
The expected source range is270 to350 lines. HARD STOP350 before more source or a check.
The only two proposed helpers are prefix composition and actual scan-boundary completion.
Keep default declaration limits and all linters. Preserve any stopped draft and exact repairs.

This remains a noncomputable operational model. Physical pruning equivalence,
hash grouping, generated parents, Mu unfolding/reconstruction, full traversal,
the public pass and Haskell refinement remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem.

Refresh upstream and record a fresh baseline before the next component.
Preserve every earlier proof, counterexample, repair, draft and the optimized core.
Keep the Haskell repair index FIRST in FINDINGS. No Haskell repair is added here.
Remote publication needs fresh user approval after the earlier automatic rejection.
'''
assert not (HERE / 'NEXT-TARGET.md').exists()
(HERE / 'NEXT-TARGET.md').write_text(text)
note = ROOT / 'lean/notes-current-original-row-cluster-control.md'
with note.open('a') as stream:
    stream.write('\nThe exact next contract is in lean/restart-evidence/20261022-original-row-cluster-control/NEXT-TARGET.md.\n')
    stream.write('Only a context, public header and helper-statement proposal is authorized next.\n')
    stream.write('The hard source stop is350 lines. Bodies and checks need separate complete review.\n')
print(json.dumps(gate))
