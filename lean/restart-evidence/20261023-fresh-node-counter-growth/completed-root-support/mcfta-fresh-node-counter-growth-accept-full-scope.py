exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-fresh-node-counter-growth-full-tool-plan')
review = Path('/tmp/mcfta-fresh-node-counter-growth-full-plan-audit')
checked_package(owner, '19906b87e039eb2b8099c295f5ff353c6f0789b026856e8edd84270c054e95f5', '2d8f238d21b66587301f690ffb1bdcbefdd50e39596d0ea5cf98d05eb774578c')
checked_package(review, '54a5f62c7a6e3e20fe6dd665d1482c80b292e924bbc187c9b4f2a553f2daf956', '34585a4f5d3e76f1dd90b2007413778f5f6e12acd3ca924ca10ac15c8daedf6d')
assert sha(review / 'review.json') == 'f24661d13a8a8f96b94eea91b9abfe9267e6ffc04567d7af1b39d6e33b67e5b9'
assert load(review / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'root-declaration-gate.json')['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
archive(owner, 'full-tool-plan')
archive(review, 'full-plan-audit')
save('root-full-tool-scope-gate.json', dict(status='ACCEPTED_SOURCE_ONLY_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    module=NAME, basis_whole_lines=203, basis_assertions=64, root_complete_plan_map_crosswalk_and_bases_read=True,
    independent_review_sha256=sha(review / 'review.json'), declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    public_heads=['build_mono','buildMany_mono','buildEdges_mono'], private_helpers=['work_mono','bind_mono','request_mono'],
    contracts_count=10, compiled_fragment_lines=46, context_lines=9, private_header_lines=18, public_header_lines=12,
    source_hard_stop=180, diagnostic_tail_lines=20, materializer_cli_arguments=7,
    selected_target=[203,210], selected_hard_stop=220, selected_authorship_authorized=True,
    selected_activation_authorized=False, clean_actual_strict_and_whole_selected_source_review_required=True,
    actual_future_receipts_and_type_results_unbound=True, default_limits_and_all_linters_preserved=True,
    generic_guard_families_preserved=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED reviewed FULL scope. Selected source authorship only; no execution until clean strict and selected-source review.')
