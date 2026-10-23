exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
import sys
plan = Path('/tmp/mcfta-rebuild-admission-full-tool-plan')
audit = Path('/tmp/mcfta-rebuild-admission-full-plan-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(plan, 'fd6ca2e7fceac329d2534f70e20f207b038b0b0a7d796275b1040c7fb91ff26f', '20fda4d20452789e7c4458905e5fb3c015d9dad59c0ee79cdfa0dab60dc77e6e')
checked_package(audit, expected_pins, expected_freeze)
assert sha(audit / 'review.json') == expected_review
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'selected-source-gate.json')['source_lines'] == 90
archive(plan, 'full-tool-plan')
archive(audit, 'full-plan-audit')
save('root-full-tool-scope-gate.json', dict(status='ACCEPTED_EXACT_TWO_TOOL_SCOPE_BEFORE_AUTHORING',
    module=NAME, public_heads=['rebuilt_admitted'], plan_sha256=sha(plan / 'plan.md'),
    independent_review_sha256=expected_review, root_whole_plan_lines_read=24,
    root_complete_predecessor_lines_read=203, selected_tool_target_lines=203,
    whole_selected_tool_hard_stop=210, all_generic_guard_families_required=True,
    mandatory_seven_CLI_fields_unchanged=True, actual_owned_strict_snapshot_path_unchanged=True,
    canonical_module_snapshot_absent_until_once_only_materialization=True,
    actual_strict_gate_sha256=sha(HERE / 'selected-source-gate.json'),
    selected_tool_authoring_accepted=True, selected_program_execution_accepted=False))
print('ACCEPTED exact source-only FULL tool scope for the actual selected strict source.')
