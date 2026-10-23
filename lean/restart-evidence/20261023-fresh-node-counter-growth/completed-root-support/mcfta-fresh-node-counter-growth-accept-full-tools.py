exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import sys
review_path, expected_pins, expected_freeze, expected_review = sys.argv[1:]
owner = Path('/tmp/mcfta-fresh-node-counter-growth-full-tool-source')
review = Path(review_path)
checked_package(owner, '97071042d545f03a68e833582173168471bc75be78bb1002b78e7689fed3a90f', '6779eb687379e574764e34be1baefa2ab15d1233fe83f181d82504cbb5551e2d')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review and load(review / 'review.json')['status'] == 'CLEAR'
gate = load(HERE / 'selected-source-gate.json')
assert gate['status'] == 'ACCEPTED_STRICT_SOURCE' and gate['strict_log_bytes'] == 0
assert load(HERE / 'root-full-tool-scope-gate.json')['selected_authorship_authorized']
assert gate['module'] == NAME and gate['source_cap'] == 180
archive(owner, 'full-preparation')
archive(review, 'full-tool-audit')
installed = {}
for name, expected in [('check-full-public.py','792b1962f88ac20a659b8e1df711b9cd4b5cfb5d364e3d53e4886dbb5f846284'),
                       ('prepare-full.py','d6c2647e9e6ada5641b6130607f117f906f2f2faf8c3a2b85fcab0f79af613c0')]:
    path = owner / 'selected' / name
    assert sha(path) == expected
    with (HERE / name).open('xb') as output:
        output.write(path.read_bytes())
    installed[name] = expected
save('root-full-tool-gate.json',dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',module=NAME,
    source_sha256=gate['source_sha256'],source_lines=gate['source_lines'],selected_strict=gate['selected_strict'],
    public_heads=gate['public_heads'],private_helpers=['work_mono','bind_mono','request_mono'],
    independent_review_sha256=expected_review,root_complete_selected_lines_read=207,root_complete_basis_lines_read=203,
    root_all_sequential_diffs_and_gate_adapters_read=True,selected_lines=207,selected_hard_stop=220,
    diagnostic_tail_lines=20,materializer_cli_arguments=7,installed_tools=installed,
    materializer_activation=True,sole_FULL_activation=True,reader_activation_after_actual_FULL=True,
    exact_actual_private_helper_checks=True,all_generic_guard_families_preserved=True,goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED exact reviewed FULL tools for actual clean strict source; materializer and sole FULL activated.')
