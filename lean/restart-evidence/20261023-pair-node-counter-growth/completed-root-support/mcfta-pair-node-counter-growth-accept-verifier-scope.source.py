exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-pair-node-counter-growth-proof-verifier-scope-plan')
peer = Path('/tmp/mcfta-pair-node-counter-growth-proof-verifier-scope-audit')
checked_package(owner, '5c56a66f7ea6edf82be0b687cc18a28c4bed268d6a4f0390d5bf5e1b00e77340', 'cba1c7fc1eead380e230b01e93bb4590d49915b7c5ebd9ceace130ccfb83b67d')
checked_package(peer, '1a4a2cfd7e8322805e2e9adb8f9a24e2959662d6c7f99be134331a8ee3133a6a', 'f595b7c8034b970b373557b7723cdd7fb7e240a9a281d4247f2ec8d33013397f')
assert sha(peer / 'review.json') == '901bec33d77cb2a67c4c3c915b41b5ec84643430a01d9f7672e9b537bbc6ffec'
assert load(peer / 'review.json')['status'] == 'CLEAR'
basis = ROOT / 'lean/restart-evidence/20261023-demand-node-counter-growth'
assert sha(basis / 'verify-proofs.py') == 'fd39f4d26ce0c8baa121499c9c5d765ad40138dfe4d8b629ffa95659c7207f3d'
assert sha(basis / 'bound-data.json') == '578f78cd7fe8979714090136f08184880c885e0068229bacf175c4a81a664b10'
crosswalk = load(owner / 'guard-crosswalk.json')
nodes = sorted((node for node in ast.walk(ast.parse((basis / 'verify-proofs.py').read_text())) if isinstance(node, ast.Assert)), key=lambda node:node.lineno)
assert len(nodes) == len(crosswalk['rows']) == 224
for node, row in zip(nodes, crosswalk['rows'], strict=True):
    assert node.lineno == row['basis_line']
    assert ast.dump(node.test) == ast.dump(ast.parse(row['basis_expression'], mode='eval').body)
assert sum(row['action']=='KEEP_GENERIC_EXPRESSION_EXACT_WITH_MULTIPLICITY' for row in crosswalk['rows']) == 174
archive(owner, 'proof-verifier-scope-plan')
archive(peer, 'proof-verifier-scope-audit')
save('root-proof-verifier-scope-gate.json', dict(status='ACCEPTED_SOURCE_ONLY_SAVED_VERIFIER_SCOPE',
    module=NAME, root_complete_38_line_plan_and_all_maps_read=True,
    previous_complete_basis_424_and_data_530_read_reused_after_exact_identity=True,
    all_50_checkpoint_specific_guard_expressions_read=True, all_224_crosswalk_rows_checked=True,
    generic_exact_AST_expressions_with_multiplicity=174, checkpoint_scope_adapters=50,
    selected_target=[424,440], selected_hard_stop=450, no_new_abstraction=True,
    actual_Root_body_declaration_and_TYPE_schemas_required=True,
    literal_per_kind_header_attachments_and_exact_accessor_match_required=True,
    external_full_command_and_raw_occurrence_count_required=True,
    future_values_remain_rejecting_until_actual=True, independent_review_sha256=sha(peer / 'review.json'),
    selected_authoring_authorized=True, selected_activation_authorized=False))
print('Accepted saved-verifier source scope. Actual data and complete selected review remain required.')
