import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
readback = json.loads((HERE / 'public-readback/direct-edge-word-ranges-full-readback.json').read_text())
checked = (HERE / 'public-readback/direct-edge-word-ranges-edge_body-public-type.txt').read_bytes()
printed = (HERE / 'public-readback/direct-edge-word-ranges-edge_body-printed-public-type.txt').read_bytes()
assert checked == printed and len(checked.splitlines()) == 150 and len(checked) == 11721
assert hashlib.sha256(checked).hexdigest() == 'dea801f02c35eb6ba68479e8fb93702264bf3b802aca8e06694683f988e9becf'
assert readback['source_sha256'] == 'de874220ae0aab490300f809c9fa4d2a931030fd69b95efb70deaa9a92a4b440'
assert readback['source_lines'] == 44 and readback['owned_public_job_exit'] == 0
assert readback['heads'][0]['private_namespace_helpers_checked'] == []
assert readback['heads'][0]['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
independent = (HERE / 'public-type-audit/review.md').read_bytes()
assert hashlib.sha256(independent).hexdigest() == '194e2f0b31e46260216d2873be04a1885a7550aa6224524595461e64ce12bc8b'
assert b'ACCEPTED PUBLIC TYPE CLEAR' in independent
assert not (HERE / 'direct-edge-word-ranges-audit-1.json').exists()
review = {
    'status': 'ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    'source_sha256': readback['source_sha256'], 'source_lines': 44,
    'public_theorem': 'MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges.edge_body',
    'complete_public_type_root_review': 'CLEAR',
    'independent_complete_public_type_review': 'CLEAR',
    'root_read_both_complete_type_files': True,
    'check_print_type_byte_identity': True,
    'four_private_markers_and_all_helpers_absent_from_type': True,
    'type_sha256': hashlib.sha256(checked).hexdigest(),
    'type_logical_lines': 150, 'type_lf': 149, 'type_bytes': 11721,
    'full_raw_sha256': readback['log_sha256'],
    'actual_axioms': readback['heads'][0]['actual_axioms'],
    'body_retained_and_programmatically_checked': True,
    'whole_body_manual_read_claimed': False,
    'word_ranges_derived': True, 'every_raw_steps_prefix': True,
    'actual_source_current_readiness_and_room_premises': True,
    'future_success_premise': False, 'native_completion_claimed': False,
    'official_install_authorized': True, 'audit_pass_claimed': False,
    'proof_jobs_at_review': 2, 'source_jobs_at_review': 2, 'audit_jobs_at_review': 0,
    'precheck_qualification_repair_is_not_a_failed_lean_job': True,
    'remote_publication': 'PENDING_USER_APPROVAL',
}
assert not (HERE / 'root-full-review.json').exists()
(HERE / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
