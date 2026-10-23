exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-demand-node-counter-growth-publication-scope-plan')
peer = Path('/tmp/mcfta-demand-node-counter-growth-publication-scope-audit')
checked_package(owner, 'f3a1d3f7ad9e65eb785236aa246424982852915d6e448e755b0003b7b283f9e2', 'e05d688520db43adcaf05008ca17aad4bf94f3e1b8bafce69e4d8a954fbeca6d')
checked_package(peer, '61879edd638863a34dc5478660e4fe9dd58d26dfd4d864ff3937063dcb8e20fb', '996afb44da151f20644fbf1fb2f39e17179f4e59bb9183b6f593ef8ae4c46f77')
assert sha(peer / 'review.json') == '7c9c10b580f0cd24b8062ba5a919dae6be2af76523d29129853a92f01af2c567'
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and not review['reviewer_scope_or_three_tool_author']
inputs = load(owner / 'input-map.json')
assert inputs['START'] == START and inputs['module'] == NAME
assert inputs['common_helper']['sha256'] == sha(HERE / 'root-common.py')
count = 0
for name, item in inputs['basis'].items():
    source = owner / item['snapshot']
    assert source.read_bytes() == Path(item['path']).read_bytes() and sha(source) == item['sha256']
    assert len(source.read_text().splitlines()) == item['lines']
    observed = [node for node in ast.walk(ast.parse(source.read_text())) if isinstance(node, ast.Assert)]
    assert len(observed) == item['AST_assertions']
    count += len(observed)
assert count == 44
crosswalk = load(owner / 'guard-crosswalk.json')
assert crosswalk['whole_basis_lines'] == 101 and len(crosswalk['rows']) == 44
for row in crosswalk['rows']:
    tree = ast.parse((owner / 'basis' / row['basis_file']).read_text())
    assertions = {node.lineno: ast.unparse(node.test) for node in ast.walk(tree) if isinstance(node, ast.Assert)}
    assert assertions[row['line']] == row['expression']
archive(owner, 'publication-scope-plan')
archive(peer, 'publication-scope-audit')
save('root-publication-scope-gate.json', dict(status='ACCEPTED_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    root_whole_plan_input_map_crosswalk_and_complete_bases_read=True,
    basis_lines=101, assertions=44, source_target=101, source_hard_stop=115,
    all_generic_guards_retained=True, independent_review_sha256=sha(peer / 'review.json'),
    actual_source_SHA_and_final_results_stage_specific=True,
    future_fields_remain_rejecting=True, local_publisher_network_free=True,
    authorized_Root_push_separate=True, selected_authorship_authorized=True,
    activation_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the three publication tool scopes. Selected authorship is authorized; installation and execution remain gated.')
