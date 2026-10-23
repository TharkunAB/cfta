exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
plan = Path('/tmp/mcfta-group-admission-full-tool-plan')
checked_package(plan,'3bedd5c62c2a9ab62752a14e918581650b6558c28445811030dccf2e3eada6af','7e7244e59fc2dde0527ac71202070a8a31abf2b419ac2ed6482cc782ece8599d')
audit = Path('/tmp/mcfta-group-admission-full-plan-audit')
checked_package(audit,'bad6db85e060f019c00816d8276d157a0d9485d9dfb525be1f6cb1b4eda2ca05','d38026940c0630bfa4174f167f27e575497d9f9ab33db68447754357076b1b1a')
assert load(audit / 'review.json')['status'] == 'CLEAR'
selected = load(HERE / 'selected-source-gate.json')
assert selected['status'] == 'ACCEPTED_STRICT_SOURCE' and selected['strict_log_bytes'] == 0
working, retained = HERE / (NAME + '.lean'), HERE / 'strict-selected-source.lean'
assert not retained.exists()
assert sha(working) == selected['source_sha256']
assert working.read_bytes() == (HERE / 'strict1.source.lean').read_bytes()
archive(plan,'full-tool-plan')
archive(audit,'full-plan-audit')
working.rename(retained)
save('source-working-copy-rename.json',dict(status='EXACT_WORKING_COPY_RETAINED_BEFORE_ONCE_ONLY_MATERIALIZER',
    old_path=working.name, retained_path=retained.name, source_sha256=sha(retained),
    reason='Keep the inherited materializer nonoverwrite guard. Its canonical snapshot must be created once from the actual strict source.',
    frozen_variant_and_strict_source_unchanged=True, mathematical_source_change=False))
save('root-full-tool-scope-gate.json',dict(status='ACCEPTED_EXACT_TOOL_ADAPTATION_SCOPE_BEFORE_AUTHORING',
    module=NAME, public_heads=['groups_admitted'], source_sha256=selected['source_sha256'], source_lines=100,
    selected_strict='strict1', selected_source_gate_sha256=sha(HERE / 'selected-source-gate.json'),
    independent_plan_review_sha256=sha(audit / 'review.json'), root_whole_plan_lines_read=28,
    root_whole_predecessor_lines_read=201, whole_selected_tool_hard_stop=210,
    approved_bindings=dict(evidence_directory=str(HERE),contract_directory='declaration-plan',gate_filename='root-declaration-gate.json',
        archive_component='full-preparation',active_reader='check-full-public.py',active_materializer='prepare-full.py',
        full_stem='FULL1',artifact_prefix='group-admission'),
    diagnostic_tail_lines=14, source_limits_unchanged=True,
    all_guard_families_required=True, no_checker_framework=True,
    selected_source_authoring_accepted=True, tool_installation_or_execution_accepted=False))
print('ACCEPTED exact FULL tool adaptation scope; working bytes retained without overwriting the future snapshot.')
