import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
prefix = 'public-readback/same-symbol-edge-original-rows-'
readback = json.loads((HERE / (prefix + 'full-readback.json')).read_text())
checked = (HERE / (prefix + 'both_miss_complete-public-type.txt')).read_bytes()
printed = (HERE / (prefix + 'both_miss_complete-printed-public-type.txt')).read_bytes()
assert checked == printed and len(checked.splitlines()) == 1085 and len(checked) == 111209
assert hashlib.sha256(checked).hexdigest() == '1fafa42dc1da4f085fba4095ceead64712ad62a11afa819d07fc7bf7b79ab7e1'
assert readback['source_sha256'] == '9d8af23bc2bbdd97f462a34b4d786d772a55bebf243dd585187b25630ac6440b'
assert readback['source_lines'] == 174 and readback['owned_public_job_exit'] == 0
assert readback['heads'][0]['private_namespace_helpers_checked'] == ['original_of_readback', 'rows_scope']
assert readback['heads'][0]['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
independent = (HERE / 'public-type-audit/review.md').read_bytes()
assert hashlib.sha256(independent).hexdigest() == sys.argv[1]
assert not (HERE / 'same-symbol-edge-original-rows-audit-1.json').exists()
review = {
    'status': 'ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    'source_sha256': readback['source_sha256'], 'source_lines': 174,
    'public_theorem': 'MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRows.both_miss_complete',
    'complete_public_type_root_review': 'CLEAR',
    'independent_complete_public_type_review': 'CLEAR',
    'root_read_complete_public_type': True,
    'root_printed_type_byte_identity_verified': True,
    'root_manual_type_ranges': [[1, 220], [221, 440], [441, 660], [661, 880], [881, 1085]],
    'check_print_type_byte_identity': True,
    'four_private_markers_and_all_helpers_absent_from_type': True,
    'type_sha256': hashlib.sha256(checked).hexdigest(),
    'type_logical_lines': 1085, 'type_lf': 1084, 'type_bytes': 111209,
    'full_raw_sha256': readback['log_sha256'],
    'actual_axioms': readback['heads'][0]['actual_axioms'],
    'body_retained_and_programmatically_checked': True,
    'whole_body_manual_read_claimed': False,
    'native_and_wrapper_completion_derived': True,
    'native_completion_derived': True,
    'original_closed_parent_rows': True,
    'source_scope_and_current_readiness_derived': True,
    'semantic_completion_and_word_ranges_derived': True,
    'final_stable_and_native_idle_derived': True,
    'same_receipt_and_captured_returned_cells': True,
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
