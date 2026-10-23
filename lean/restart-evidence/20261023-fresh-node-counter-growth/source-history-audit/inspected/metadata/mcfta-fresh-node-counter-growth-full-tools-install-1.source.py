exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
owner=Path('/tmp/mcfta-fresh-node-counter-growth-full-tool-source-v3')
review=Path('/tmp/mcfta-fresh-node-counter-growth-full-tool-v3-audit')
checked_package(owner,'318b1f192a7deb3797abb25735b926f1de8173210fa0e7b55733d8a09e911477','262794e339730d49763317ab6ab7ded1883d22a06b5885f080d97a428e32f26b')
checked_package(review,'8116d391fc7bc2df4d7292b9d7df925decd59b2422d9f47d11274381fe7fb926','356b1830eb7dc7ffc4b0e63d9ee29e49cb7b4eccff5dae1e805e2e0c8e5089fd')
assert sha(review/'review.json')=='62aa687defe7e70f700fec40ca6b0ddf695e2fc7f5e10d823875883ec3bc7079'
assert load(review/'review.json')['status']=='CLEAR'
gate=load(HERE/'selected-source-gate.json')
assert gate['status']=='ACCEPTED_STRICT_SOURCE' and gate['selected_strict']=='strict3' and gate['strict_log_bytes']==0
assert gate['declaration_gate']=='root-declaration-gate-v3.json' and gate['body_gate']=='root-body-gate-v4.json'
assert load(HERE/'root-full-tool-scope-gate-v3.json')['selected_authorship_authorized']
archive(owner,'full-preparation')
archive(review,'full-tool-v3-audit')
archive(Path('/tmp/mcfta-fresh-node-counter-growth-full-tool-audit'),'full-tool-v1-paused-audit')
prior=Path('/tmp/mcfta-fresh-node-counter-growth-full-tool-v2-audit')
checked_package(prior,'0e43e609a86e6f6c2506e3a8032fd0d84c99d0ed4edd4f349d420fd966ea9e0d','7f856f6318cb8190832b9100a33a4f850376caf82891de885f6b705dc0c6f159')
archive(prior,'full-tool-v2-audit')
installed={}
for name,expected in [('check-full-public.py','792b1962f88ac20a659b8e1df711b9cd4b5cfb5d364e3d53e4886dbb5f846284'),
                      ('prepare-full.py','015a897abb35947478c01aaeacad1b436b9d9b3e9fc714fc9811d80bafc9be8f')]:
    path=owner/'selected'/name
    assert sha(path)==expected
    with (HERE/name).open('xb') as output:
        output.write(path.read_bytes())
    installed[name]=expected
save('root-full-tool-gate.json',dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',module=NAME,
    source_sha256=gate['source_sha256'],source_lines=117,selected_strict='strict3',public_heads=gate['public_heads'],
    private_helpers=['work_mono','bind_mono','request_mono'],independent_review_sha256=sha(review/'review.json'),
    root_complete_selected_lines_read=207,root_complete_basis_lines_read=203,
    root_all_revised_sources_and_sequential_diffs_read=True,root_unchanged_reader_whole_read_and_identity_checked=True,
    selected_lines=207,selected_hard_stop=220,diagnostic_tail_lines=20,materializer_cli_arguments=7,installed_tools=installed,
    materializer_activation=True,sole_FULL_activation=True,reader_activation_after_actual_FULL=True,
    exact_actual_private_helper_checks=True,all_generic_guard_families_preserved=True,goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED selected FULL tools V3 for actual clean strict3. All historical tools and reviews retained.')
