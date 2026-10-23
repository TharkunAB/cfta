exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import ast
owner = Path('/tmp/mcfta-native-node-counter-growth-verifier-scope-plan')
review = Path('/tmp/mcfta-native-node-counter-growth-verifier-scope-audit')
checked_package(owner, '6a056afcb0967804c1b8c41c64c582f5352bbc266fbe6821440ae8bdb7f9fb1a', 'c435e8cf95416cdd9014e6f03c13f6f8698052a18e460fffc03255d80eeb4e2f')
checked_package(review, 'e6b3fb5a82d6bca59ac1a90d3833a536b7aa8cf51d2354c56ae16c2126e30ca5', '1efff491f9bd7a8cbd3691c42b76c4ca0df4c114b3ba5ebc96deeac89ba131cf')
assert load(review / 'review.json')['status'] == 'CLEAR'
adaptation = load(owner / 'adaptation-map.json')
for entry in adaptation['basis'].values():
    assert sha(Path(entry['path'])) == entry['sha256']
    assert (owner / entry['snapshot']).read_bytes() == Path(entry['path']).read_bytes()
for entry in adaptation['declaration_inputs']:
    assert sha(Path(entry['path'])) == entry['sha256']
    assert (owner / entry['snapshot']).read_bytes() == Path(entry['path']).read_bytes()
crosswalk = load(owner / 'guard-crosswalk.json')
assert [crosswalk[key] for key in ['basis_AST_assertions', 'generic_assertions_kept_exactly', 'H34_specific_assertions_replaced']] == [212, 174, 38]
tree = ast.parse((owner / 'basis/verify-proofs.py.txt').read_text())
assertions = {node.lineno: ast.unparse(node.test) for node in ast.walk(tree) if isinstance(node, ast.Assert)}
assert len(assertions) == 212
for row in crosswalk['rows']:
    assert assertions[row['basis_line']] == row['basis_expression']
assert sum(row['action'] == 'KEEP_GENERIC_GUARD' for row in crosswalk['rows']) == 174
archive(owner, 'verifier-scope-plan')
archive(review, 'verifier-scope-audit')
save('root-proof-verifier-scope-gate.json', dict(status='ACCEPTED_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    root_whole_plan_lines_read=38, root_whole_adaptation_map_and_scope_crosswalk_read=True,
    root_complete_sealed_basis_lines_read=404, root_basis_data_lines=483,
    basis_assertions=212, generic_assertions_kept=174, scope_assertions_adapted=38,
    source_target=[414, 420], source_hard_stop=430, no_padding=True,
    three_public_bodies_zero_helpers=True, exact_six_fragments_29_lines=True,
    full_generalized_IH_and_single_actual_yielded_call=True, six_specialized_equation_types=True,
    independent_review_sha256=sha(review / 'review.json'),
    declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    selected_authorship_authorized=True, future_actual_outputs_remain_rejecting=True,
    activation_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the saved-proof-verifier scope; selected source authorship is authorized, execution remains gated.')
