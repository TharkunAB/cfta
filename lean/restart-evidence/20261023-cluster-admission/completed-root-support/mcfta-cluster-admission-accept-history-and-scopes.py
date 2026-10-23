exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
packages = [
    ('/tmp/mcfta-cluster-admission-source-history-audit', 'aecd98a6eac92b1159806e5439a20719d7021c00b99e1a544d60f97c31d8d56d', '39521dc9f32e93f5efb5800d8bf7f8025446803492038806d509c165d1c7bb11', 'source-history-audit'),
    ('/tmp/mcfta-cluster-admission-proof-verifier-plan', '91246e67b614c2075830243acaad43b66699365efc60d44796c2f905415e39ff', 'ddc5cf0efbc53aacabc6612b1e9202bdb359c83b1065c843dcf599af1aa7d2b4', 'proof-verifier-plan'),
    ('/tmp/mcfta-cluster-admission-proof-verifier-plan-audit', '4aa69e1eb17d808d67750832cf7891745ba9e84958f514c17afe638664a7316f', '81c4740cf9bc02ff3abc439ab75f774314eef0bab22a74181c904517942a843d', 'proof-verifier-plan-audit'),
    ('/tmp/mcfta-cluster-admission-closing-tool-plan', 'eeec20838b0e3c8a2b3b76a80ed2fe45536246d641686e0f8ed8ad924fb909d9', '18f63c0eda0302326d0b6b501e637b75edc0b25c7b027c8561e680c942203fff', 'closing-tool-plan'),
]
for path, pins, frozen, _archive_name in packages:
    checked_package(Path(path), pins, frozen)
history = load(Path(packages[0][0]) / 'review.json')
assert history['status'] == 'CLEAR' and history['source_history_gate_sha256'] == sha(HERE / 'source-history-gate.json')
assert history['actual_counts']['total_jobs'] == 12 and history['actual_counts']['Audit_dependencies'] == 75525
assert load(Path(packages[2][0]) / 'review.json')['status'] == 'CLEAR'
for path, _pins, _frozen, archive_name in packages:
    archive(Path(path), archive_name)
save('root-source-history-review.json', {
    'status': 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    'root_whole_selected_source_lines_read': 399,
    'root_all_six_complete_public_TYPEs_read': True,
    'source_history_sha256': sha(HERE / 'source-history-gate.json'),
    'independent_review_sha256': sha(HERE / 'source-history-audit/review.json'),
    'actual_jobs': 12, 'source_jobs': 9, 'focused_build_jobs': 2, 'audit_jobs': 1,
    'failed_source_jobs': 3, 'root_metadata_cut_jobs': 40, 'failed_root_metadata_jobs': 2,
    'new_theorem_result_claimed': False, 'goal_status': 'ACTIVE_INCOMPLETE',
})
save('root-proof-verifier-scope-gate.json', {
    'status': 'ACCEPTED_SOURCE_ONLY_SCOPE_BEFORE_SELECTED_EXECUTABLE',
    'root_whole_plan_lines_read': 45,
    'independent_plan_review_sha256': sha(HERE / 'proof-verifier-plan-audit/review.json'),
    'module_count': 3, 'public_theorems': 6, 'ordinary_code_hard_stop': 450,
    'selected_authoring_authorized': True, 'installation_or_execution_authorized': False,
    'actual_history_gate_sha256': sha(HERE / 'source-history-gate.json'),
})
save('root-closing-tools-scope-gate.json', {
    'status': 'ACCEPTED_SOURCE_ONLY_SCOPE_BEFORE_SELECTED_EXECUTABLE',
    'root_whole_plan_lines_read': 23, 'root_whole_predecessor_lines_read': 229,
    'program_count': 5, 'ordinary_code_hard_stop': 260,
    'selected_authoring_authorized': True, 'installation_or_execution_authorized': False,
    'authorship': 'Root authored all current mathematical bodies. Arity authored declaration and current tool adaptations.',
})
print('PASS: independent source/history review accepted and both closing tool scopes recorded')
