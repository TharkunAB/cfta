import ast
import importlib.util
import sys
from pathlib import Path

spec = importlib.util.spec_from_file_location('common', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py')
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)
owner = Path('/tmp/mcfta-scan-node-counter-growth-proof-verifier-scope-plan')
peer = Path('/tmp/mcfta-scan-node-counter-growth-proof-verifier-scope-review')
common.checked_package(owner, 'b6bcf4a214f2c683410e7c09e212155acec482da22acf2e12f7465bb7e0de787', '6777eee32a47fcc0472bf799a6658b165edb5040e639f68595909816934c9c49')
common.checked_package(peer, sys.argv[1], sys.argv[2])
assert common.sha(peer / 'review.json') == sys.argv[3]
assert common.load(peer / 'review.json')['status'] == 'CLEAR'
inputs = common.load(owner / 'input-map.json')
assert common.sha(owner / 'basis/verify-proofs.py') == inputs['basis']['code']['sha256'] == '9c6b2e7e537f8e5b04ba45bb9acdd8342cee905ae2d00871a3c94f6dd621c79f'
assert common.sha(owner / 'basis/bound-data.json') == inputs['basis']['data']['sha256'] == '1e12cb608db0a52a00d4e4838d72777a2ee3607e34a15d13904fcc83b4174985'
assert len((owner / 'basis/verify-proofs.py').read_text().splitlines()) == 428
assert len((owner / 'basis/bound-data.json').read_text().splitlines()) == 583
crosswalk = common.load(owner / 'guard-crosswalk.json')
assert (crosswalk['basis_assertions'], crosswalk['exact_generic_AST_with_multiplicity'], crosswalk['inherited_scope_data_or_accessor_obligations'], crosswalk['new_H38_scope_obligations']) == (227, 174, 53, 2)
actual = sorted((n for n in ast.walk(ast.parse((owner / 'basis/verify-proofs.py').read_text())) if isinstance(n, ast.Assert)), key=lambda n:n.lineno)
assert [(r['basis_line'], r['basis_expression']) for r in crosswalk['rows']] == [(n.lineno, ast.unparse(n.test)) for n in actual]
assert sum(r['classification'] == 'EXACT_GENERIC_RETAIN_WITH_MULTIPLICITY' for r in crosswalk['rows']) == 174
for name, pin in inputs['actual_known_inputs'].items():
    assert common.sha(Path(pin['path'])) == pin['sha256'] == common.sha(owner / 'actual-inputs' / name)
assert inputs['source_lines'] == 80 and inputs['source_cap'] == 140
assert (inputs['exact_contract_count'], inputs['exact_contract_lines']) == (6, 29)
common.archive(owner, 'proof-verifier-scope-plan')
common.archive(peer, 'proof-verifier-scope-audit')
common.save('root-proof-verifier-scope-gate.json', {
    'status':'ACCEPTED_SOURCE_ONLY_SAVED_VERIFIER_SCOPE', 'module':common.NAME,
    'root_whole_scope_plan_and_all_53_scope_data_accessor_obligations_read':True,
    'complete_sealed_428_line_code_and_583_line_data_basis_identity_checked':True,
    'prior_complete_basis_reads_reused_by_exact_sealed_identity':True,
    'all_227_actual_AST_assertions_correlate':True,
    'all_174_generic_AST_expressions_and_multiplicities_retained':True,
    'exact_actual_gate_schema_adapters_read':True,
    'raw_qualified_and_own_accessor_counts':[ [0,11,6], [0,6,0], [0,5,6] ],
    'exact_external_H37_command_and_raw_body_restore_required':True,
    'selected_target':[430,440], 'selected_hard_stop':450,
    'independent_review_sha256':common.sha(peer / 'review.json'),
    'selected_code_authoring_authorized':True,
    'future_result_data_rejecting_until_actual':True,
    'selected_activation_requires_complete_source_and_actual_data_review':True,
    'goal_status':'ACTIVE_INCOMPLETE'})
print('PASS: exact source-only saved-verifier scope accepted; future result bindings remain rejecting.')
