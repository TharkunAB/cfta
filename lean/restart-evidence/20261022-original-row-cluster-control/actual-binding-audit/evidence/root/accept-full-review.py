import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
prefix = 'public-readback/original-row-cluster-control-'
readback = json.loads((HERE / (prefix + 'full-readback.json')).read_text())
checked = (HERE / (prefix + 'comparison_lift-public-type.txt')).read_bytes()
printed = (HERE / (prefix + 'comparison_lift-printed-public-type.txt')).read_bytes()
assert checked == printed and len(checked.splitlines()) == 136 and len(checked) == 9947
assert hashlib.sha256(checked).hexdigest() == 'dbd38ee0a0aaa0fce6403114f3257eb86a3c77bac91adb273e9c04437b0c1f81'
assert readback['source_sha256'] == '37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7'
assert readback['source_lines'] == 129 and readback['owned_public_job_exit'] == 0
assert readback['heads'][0]['private_namespace_helpers_checked'] == []
assert set(readback['heads'][0]['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
independent = (HERE / 'public-type-audit/review.md').read_bytes()
assert hashlib.sha256(independent).hexdigest() == sys.argv[1]
assert not (HERE / 'original-row-cluster-control-audit-1.json').exists()
review = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    source_sha256=readback['source_sha256'], source_lines=129,
    public_theorem='MicroCFTA.SourceCurrentOriginalRowClusterScan.comparison_lift',
    complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_read_complete_public_type=True, root_manual_type_ranges=[[1, 136]],
    root_printed_type_byte_identity_verified=True, check_print_type_byte_identity=True,
    four_private_markers_and_all_helpers_absent_from_type=True,
    type_sha256=hashlib.sha256(checked).hexdigest(), type_logical_lines=136,
    type_lf=135, type_bytes=9947, full_raw_sha256=readback['log_sha256'],
    actual_axioms=readback['heads'][0]['actual_axioms'],
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    completed_comparison_observation_premise=True, comparison_lift_derived=True,
    same_h7_full_state_and_residuals_retained=True, all_five_comparison_outcomes_forwarded=True,
    candidate_identity_before_pivot_identity=True, promotion_reconstruction_order_preserved=True,
    positive_consumed_prefix_at_most_supplied_fuel=True, exact_inline_resume_same_after=True,
    noncomputable_operational_model=True, genuine_packet_cluster_completion_claimed=False,
    physical_language_iff_claimed=False, scan_completion_claimed=False,
    future_success_premise=False, semantic_completion_premise=False,
    word_ranges_premise=False, post_room_premise=False, generated_parent_oracle=False,
    official_install_authorized=True, audit_pass_claimed=False,
    proof_jobs_at_review=3, source_jobs_at_review=3, failed_jobs_at_review=1,
    audit_jobs_at_review=0, independent_type_review_sha256=sys.argv[1],
    remote_publication='PENDING_USER_APPROVAL')
assert not (HERE / 'root-full-review.json').exists()
(HERE / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
