exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-rebuild-admission-full-preparation')
audit = Path('/tmp/mcfta-rebuild-admission-full-tools-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, 'db3a8725a7da9e52c131d5be3693818c06d997179eeee23a82c55821d27d1f11', '9245a46d2f88ec6575b963b3b0888c5ed189d1cbdbd774ea3a10af5950508bb3')
checked_package(audit, expected_pins, expected_freeze)
assert sha(audit / 'review.json') == expected_review
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'selected/check-full-public.py') == '2ffb60ee0951bb4d6656a8c542d7ede632b5055427e86b35d28620b331750277'
assert sha(owner / 'selected/prepare-selected-full.py') == '52387eed9ada4f25688a4c404582054812757b4a16d741146536c19b998132eb'
selection = load(HERE / 'selected-source-gate.json')
assert selection['source_lines'] == 90 and selection['selected_strict'] == 'strict1'
assert load(HERE / 'root-full-tool-scope-gate.json')['whole_selected_tool_hard_stop'] == 210
assert (HERE / 'strict1.log').read_bytes() == b'' and load(HERE / 'strict1.json')['exit_code'] == 0
assert not (HERE / (NAME + '.lean')).exists()
tools = {'check-full-public.py': 'check-full-public.py', 'prepare-full.py': 'prepare-selected-full.py'}
assert all(not (HERE / name).exists() for name in tools)
archive(owner, 'full-preparation')
archive(audit, 'full-tools-audit')
for active, archived in tools.items():
    (HERE / active).write_bytes((owner / 'selected' / archived).read_bytes())
save('root-full-tools-gate.json', dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    module=NAME, source_sha256=selection['source_sha256'], source_lines=90,
    public_heads=['rebuilt_admitted'], installed_tools={name:sha(HERE / name) for name in tools},
    root_whole_selected_lines_read=203, root_whole_basis_lines_read=203,
    independent_review_sha256=expected_review, all_generic_guards_retained=True,
    mandatory_seven_CLI_fields_unchanged=True, strict_snapshot_path_unchanged=True,
    diagnostic_tail_lines=14, materializer_activation=True, sole_FULL_activation=True,
    reader_activation_after_actual_FULL=True, canonical_snapshot_nonoverwrite=True,
    whole_goal_complete=False))
print('ACCEPTED and installed both whole-reviewed FULL tools for the actual selected strict source.')
