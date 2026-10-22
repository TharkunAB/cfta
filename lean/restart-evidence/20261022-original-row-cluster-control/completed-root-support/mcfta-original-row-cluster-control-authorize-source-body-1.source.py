import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
pins = {
    'context.lean.txt': '52b67b3ee986878dd27d15788e23641810666dfac6f8e1ad2e3709e0049ecee6',
    'proposed-signature.lean.txt': 'b01d01167a0b3df13c9cf6fa3419116b2d0fe3969d7676c04f3fcde765c9ccb4',
    'declaration-schema.md': '8896d609acf03d7bf69019c9f1cdddaed960e081d6cb074c4d199e9ea0564838',
}
for name, expected in pins.items():
    assert hashlib.sha256((HERE / 'signature-plan' / name).read_bytes()).hexdigest() == expected
review = (HERE / 'signature-audit/review.md').read_bytes()
assert hashlib.sha256(review).hexdigest() == sys.argv[1]
assert (HERE / 'starting-head.txt').read_text().strip() == '4f7a7e064f17a66367618dc2bc360f0755503b1a'
target = HERE / 'source-body-authorization.json'
assert not target.exists()
authorization = {
    'status': 'ROOT_APPROVED_FOR_ONE_SOURCE_PROPOSAL',
    'target': 'SourceCurrentOriginalRowClusterScan.lean',
    'context_lines': 12, 'public_header_lines': 19,
    'selected_contract_pins': pins,
    'independent_signature_review_sha256': sys.argv[1],
    'root_read_complete_context_header_schema_note': True,
    'root_read_complete_independent_signature_review': True,
    'allowed_declarations': ['Control', 'Outcome', 'step', 'execute', 'comparison_lift'],
    'definition_body_authorized': True, 'theorem_body_authorized': True,
    'compiler_authorized': False,
    'complete_source_review_required_before_compiler': True,
    'source_target_lines': [120, 180], 'source_hard_stop_lines': 220,
    'same_h7_state_and_direct_h7_step': True,
    'exact_outcomes_and_residuals_required': True,
    'candidate_identity_before_pivot_identity': True,
    'positive_consumed_prefix_at_most_supplied_fuel': True,
    'public_resume_expression_inline': True,
    'default_declaration_limits_required': True,
    'noncomputable_operational_model': True,
    'genuine_packet_cluster_completion_claimed': False,
    'physical_pruning_or_haskell_refinement_claimed': False,
    'whole_goal_complete': False,
}
target.write_text(json.dumps(authorization, indent=2) + '\n')
print(json.dumps(authorization))
