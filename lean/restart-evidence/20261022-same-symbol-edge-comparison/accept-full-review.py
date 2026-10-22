import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
prefix = 'public-readback/same-symbol-edge-comparison-'
readback = json.loads((HERE / (prefix + 'full-readback.json')).read_text())
checked = (HERE / (prefix + 'original_rows_complete-public-type.txt')).read_bytes()
printed = (HERE / (prefix + 'original_rows_complete-printed-public-type.txt')).read_bytes()
assert checked == printed and len(checked.splitlines()) == 728 and len(checked) == 69839
assert hashlib.sha256(checked).hexdigest() == '7fb94c311d5eff9aa93faa2dab7cc235a2e9dffe365b98d2c5ca04c39c49dd8d'
assert readback['source_sha256'] == '02d01576ce9e7188342835138452a5163b150e28c264c01782137848e1a1c560'
assert readback['source_lines'] == 112 and readback['owned_public_job_exit'] == 0
assert readback['heads'][0]['private_namespace_helpers_checked'] == []
assert readback['heads'][0]['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
independent = (HERE / 'public-type-audit/review.md').read_bytes()
assert hashlib.sha256(independent).hexdigest() == sys.argv[1]
assert not (HERE / 'same-symbol-edge-comparison-audit-1.json').exists()
review = {
    'status': 'ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    'source_sha256': readback['source_sha256'], 'source_lines': 112,
    'public_theorem': 'MicroCFTA.SourceCurrentSameSymbolEdgeComparison.original_rows_complete',
    'complete_public_type_root_review': 'CLEAR',
    'independent_complete_public_type_review': 'CLEAR',
    'root_read_complete_public_type': True,
    'root_printed_type_byte_identity_verified': True,
    'root_manual_type_ranges': [[1, 185], [186, 370], [371, 555], [556, 728]],
    'check_print_type_byte_identity': True,
    'four_private_markers_and_all_helpers_absent_from_type': True,
    'type_sha256': hashlib.sha256(checked).hexdigest(),
    'type_logical_lines': 728, 'type_lf': 727, 'type_bytes': 69839,
    'full_raw_sha256': readback['log_sha256'],
    'actual_axioms': readback['heads'][0]['actual_axioms'],
    'body_retained_and_programmatically_checked': True,
    'whole_body_manual_read_claimed': False,
    'original_closed_parent_rows': True,
    'all_pair_lookup_cases_covered': True,
    'same_current_operand_residency_derived': True,
    'wrapper_completion_derived': True,
    'final_stable_and_native_idle_derived': True,
    'hit_checked_state_unchanged': True,
    'native_receipt_on_hits_claimed': False,
    'actual_source_current_readiness_and_room_premises': True,
    'future_success_premise': False, 'post_call_room_claimed': False,
    'semantic_completion_premise': False, 'word_ranges_premise': False,
    'post_room_premise': False, 'generated_parent_oracle': False,
    'physical_language_iff_claimed': False,
    'official_install_authorized': True, 'audit_pass_claimed': False,
    'proof_jobs_at_review': 2, 'source_jobs_at_review': 2, 'audit_jobs_at_review': 0,
    'remote_publication': 'PENDING_USER_APPROVAL',
}
assert not (HERE / 'root-full-review.json').exists()
(HERE / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
