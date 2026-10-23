exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-demand-node-counter-growth-proof-verifier-scope')
review = Path('/tmp/mcfta-demand-node-counter-growth-proof-verifier-scope-review')
checked_package(owner, '10fd16d67164972120af2218b60395dab5686848194f12bb97f1be00dc83deb8', '52f4a06919ea99a3942e049203b620c1bd795b77f1efbdde1cb4c6cc5e9db12a')
checked_package(review, 'f6b843414c5741d92a700e5db240fb5c6b3ada4d27c53a4b86148fdae4363f5d', 'a5da9ca1b7c48edde9dfff8113697ef824a0c4012ae91fa4f1304c06d400ac13')
assert load(review / 'review.json')['status'] == 'SOURCE_ONLY_VERIFIER_SCOPE_CLEAR'
adaptation = load(owner / 'adaptation-map.json')
for entry in list(adaptation['basis'].values()) + list(adaptation['declaration_inputs'].values()):
    assert sha(Path(entry['path'])) == entry['sha256']
    assert (owner / entry['snapshot']).read_bytes() == Path(entry['path']).read_bytes()
crosswalk = load(owner / 'guard-crosswalk.json')
assert [crosswalk[key] for key in ['basis_AST_assertions', 'generic_assertions_kept_exactly', 'H35_scope_assertions_replaced']] == [221, 174, 47]
tree = ast.parse((owner / 'basis/verify-proofs.py.txt').read_text())
assertions = {node.lineno: ast.unparse(node.test) for node in ast.walk(tree) if isinstance(node, ast.Assert)}
assert len(assertions) == len(crosswalk['rows']) == 221
for row in crosswalk['rows']:
    assert assertions[row['basis_line']] == row['basis_expression']
assert sum(row['action'] == 'KEEP_GENERIC_GUARD_EXACT_EXPRESSION' for row in crosswalk['rows']) == 174
archive(owner, 'verifier-scope-plan')
archive(review, 'verifier-scope-audit')
save('root-proof-verifier-scope-gate.json', dict(status='ACCEPTED_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    root_whole_plan_lines_read=37, root_whole_adaptation_map_and_all_47_scope_rows_read=True,
    root_prior_complete_sealed_basis_418_and_data_522_read_reused_after_identity_check=True,
    all_221_crosswalk_rows_correlated_to_actual_basis_AST=True,
    basis_assertions=221, generic_assertions_kept=174, scope_assertions_adapted=47,
    source_target=[420, 428], source_hard_stop=430, no_padding=True,
    four_bodies_one_private_helper=True, exact_seven_fragments_34_lines=True,
    full_generalized_IH_and_single_actual_yielded_call=True, five_specialized_equation_types=True,
    exact_external_token_guard_dependency_view_only=True, original_raw_bodies_retained=True,
    independent_review_sha256=sha(review / 'review.json'),
    declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    selected_authorship_authorized=True, future_actual_outputs_remain_rejecting=True,
    activation_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted saved-proof verifier scope. Selected source may be prepared. Actual binding and execution remain gated.')
