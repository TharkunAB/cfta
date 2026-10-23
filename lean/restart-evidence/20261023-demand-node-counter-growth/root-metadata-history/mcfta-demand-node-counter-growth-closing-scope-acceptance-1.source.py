exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))

plan = Path('/tmp/mcfta-demand-node-counter-growth-closing-scope-plan')
peer = Path('/tmp/mcfta-demand-node-counter-growth-closing-scope-audit')
checked_package(plan, 'bdb97508e6c16c0de55fe1ff5711b4d0003fe7eea3d3f798f9ff1e79f090899c', '08bfe1a1d3defd9651e532442d7b5597e68fd40444d3ab8976618cafcddae7df')
checked_package(peer, '686fb92df180b82b19921b8b9a8e01e3bf428597b1b9be191e9dcffc1cf2465e', '2c0ca0a522da190e525cfd571dda88bf36a90f0c2c16c11610defa4aaa9f1025')
assert load(peer / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'root-declaration-gate.json')['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
bindings = load(plan / 'input-map.json')
for entry in list(bindings['basis'].values()) + bindings['known_inputs']:
    assert sha(Path(entry['path'])) == entry['sha256']
    assert (plan / entry['snapshot']).read_bytes() == Path(entry['path']).read_bytes()
previous = bindings['previous_preservation']
assert sha(Path(previous['path'])) == previous['sha256']
assert (plan / previous['snapshot']).read_bytes() == Path(previous['path']).read_bytes()
archive(plan, 'closing-scope-plan')
archive(peer, 'closing-scope-audit')
save('root-closing-scope-gate.json', dict(status='ACCEPTED_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    exact_declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    scope_plan_sha256=sha(plan / 'plan.md'), independent_review_sha256=sha(peer / 'review.json'),
    root_whole_plan_input_map_crosswalk_and_complete_bases_read=True,
    all_generic_guards_retained=True, future_actual_results_remain_rejecting=True,
    selected_authorship_authorized=True, activation_authorized=False,
    source_target=[236, 236], source_hard_stop=260))
print('Accepted closing-tool scope. Selected source may be prepared. Binding and activation require actual accepted evidence and separate review.')
