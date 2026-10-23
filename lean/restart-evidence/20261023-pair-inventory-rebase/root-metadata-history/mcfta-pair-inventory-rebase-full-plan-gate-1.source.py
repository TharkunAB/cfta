exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-pair-inventory-rebase-full-tool-plan')
review = Path('/tmp/mcfta-pair-inventory-rebase-full-plan-audit')
checked_package(owner, '66a4432cfd6a5c6013ca394d64b8e216611fb444a7900010340be881201e094d', '5a3edccb3e7da1ca0031dd630bde8fe337f7dc6a1f651c729256cf44d85b864f')
checked_package(review, '44aec6e40741cdb27a28ee5567815b2b2ead3d49453ca43db38b9c4f6896f32d', '20647718e9f6f2ccf1ef2d6dd03ff2dc5def2baedd9fe3f77ca931cbefda0ef7')
assert sha(review / 'review.json') == '984ab7e0536704702b092ada2be50a7e4c44fa22715c6508699b834406633011'
assert load(review / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'selected-source-gate.json')['status'] == 'ACCEPTED_STRICT_SOURCE'
assert sha(owner / 'plan.md') == 'f2c09eda4ddac6c44d1c24114959b69957f1a327a9c34d77aaf1953427be0a4f'
archive(owner, 'full-tool-plan')
archive(review, 'full-plan-audit')
save('root-full-tool-scope-gate.json', dict(status='ACCEPTED_EXACT_TWO_TOOL_SCOPE_BEFORE_AUTHORING',
    module=NAME, public_heads=['rebase'], plan_sha256=sha(owner / 'plan.md'),
    independent_review_sha256=sha(review / 'review.json'), root_whole_plan_lines_read=24,
    root_complete_predecessor_lines_read=203, selected_tool_target_lines=203,
    whole_selected_tool_hard_stop=210, all_generic_guard_families_required=True,
    mandatory_seven_CLI_fields_unchanged=True, actual_owned_strict_snapshot_path_unchanged=True,
    canonical_module_snapshot_absent_until_once_only_materialization=True,
    actual_strict_gate_sha256=sha(HERE / 'selected-source-gate.json'),
    selected_tool_authoring_accepted=True, selected_program_execution_accepted=False))
print('ACCEPTED exact203-line FULL-tool adaptation scope before executable authoring.')
