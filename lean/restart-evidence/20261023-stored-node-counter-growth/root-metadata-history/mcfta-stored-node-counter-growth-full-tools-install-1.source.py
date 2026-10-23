exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-stored-node-counter-growth-full-preparation-source')
review = Path('/tmp/mcfta-stored-node-counter-growth-full-tool-audit')
checked_package(owner, 'f556d6d520815a4d82d5320779ed15c096a05b5a53dcb6a4c8ec429f55a8431b', 'cf8df4bd935e6a802db1a9d55b4144553b501daf9ccf565d0adcf0e7bb7099d4')
checked_package(review, '9e2e5717cba2dfd9eec0435403204d9548f887cce6959ed0c283e6c517aa1fbb', '7d97a979bee4f13df4e17a1788e670c9afb71d8d46b2fddb51538902e44c7df6')
assert sha(review / 'review.json') == '9f6e72208651b5bb50217a05059bdbd6ef4ecfd5560eeb31365de4da06874158'
assert load(review / 'review.json')['status'] == 'CLEAR'
assert (HERE / 'strict1.log').read_bytes() == b'' and load(HERE / 'strict1.json')['exit_code'] == 0
assert sha(HERE / 'strict1.source.lean') == '2dc66e6e7cc728b051a65d622f6aab9bd236ac485b90eb4c1f60650fc438d16a'
assert not (HERE / (NAME + '.lean')).exists() and not (HERE / (NAME + '.full.lean')).exists()
archive(owner, 'full-preparation')
archive(review, 'full-tool-audit')
installed = {}
for name, expected in [('prepare-full.py','a808c09ae3ad6f576c92e606a37e3f27c7a3e01be038dd8689ad70be2fff7f14'),
        ('check-full-public.py','73502b52397f68936b21e2d375f9e7171718765377e0c3ac75de8d6c9f70c4c3')]:
    assert not (HERE / name).exists() and sha(owner / 'selected' / name) == expected
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
    installed[name] = expected
save('root-full-tool-gate.json', dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    module=NAME, source_sha256=sha(HERE / 'strict1.source.lean'), source_lines=82, selected_strict='strict1',
    public_heads=['execute_mono','unfold_mono','maybeMu_mono'],
    private_helpers=['bind_mono','callback_mono','request_mono'],
    independent_review_sha256=sha(review / 'review.json'), root_complete_selected_lines_read=209,
    root_complete_basis_lines_read=207, root_all_sources_and_exact_diffs_read=True,
    selected_lines=209, selected_hard_stop=220, diagnostic_tail_lines=20, materializer_cli_arguments=7,
    installed_tools=installed, materializer_activation=True, sole_FULL_activation=True,
    reader_activation_after_actual_FULL=True, all_generic_guard_families_preserved=True,
    canonical_nonoverwrite_guard_retained=True, early_canonical_copy_retained_as_history=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED and installed whole-reviewed FULL tools; materializer, sole FULL and reader enabled in order.')
