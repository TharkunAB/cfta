exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import ast
import sys

mode, peer_path, peer_pins, peer_freeze, peer_review = sys.argv[1:]
facts = {
    'closing':('615f3a4f289715f73b65542feaebf82653f6dcae9c88d145be55c479f4df76b2','c8040f01cd87e4a5a00418d6c7397bb6cf08efdded27c3b15326366cc3526c98',236,59,256),
    'publication':('64613616957b937d689506eb0fc41b489d4e7cf99a2117f0b35b82d354ba7c1d','645af54a3c8d25285c244b33c0d1907cb3e36ebcc140411c5b80e29a7b74cf8d',101,44,111),
    'document':('433de30f7d096a5b2e9c162333750c68366f7caf6c328d013bd99438535b9b6b','5899398c8b0974bff513c2037a8555a05494bd85a5c3b9e5dfd5829619296ddb',88,25,98)}
owner_pins, owner_freeze, lines, assertions, hard = facts[mode]
owner = Path('/tmp/mcfta-scan-node-counter-growth-' + mode + '-scope-plan')
peer = Path(peer_path)
checked_package(owner,owner_pins,owner_freeze)
checked_package(peer,peer_pins,peer_freeze)
assert sha(peer / 'review.json') == peer_review
assert load(peer / 'review.json')['status'] == 'CLEAR'
if mode == 'closing':
    manifest = load(owner / 'basis-metrics.json')['files']
    rows = load(owner / 'guard-crosswalk.json')['assertions']
    expression_key = 'expression'
else:
    manifest = load(owner / 'basis-manifest.json')['scripts']
    rows = load(owner / 'guard-crosswalk.json')['guards']
    expression_key = 'complete_expression'
actual = []
for name, pin in manifest.items():
    p = owner / 'basis' / name
    assert sha(p) == pin['sha256']
    assert len(p.read_text().splitlines()) == pin['lines']
    nodes = sorted((n for n in ast.walk(ast.parse(p.read_text())) if isinstance(n,ast.Assert)),key=lambda n:n.lineno)
    assert len(nodes) == pin['assertions']
    actual += [(name,n.lineno,ast.unparse(n.test)) for n in nodes]
assert sorted(actual) == sorted((r['file'],r['line'],r[expression_key]) for r in rows)
assert sum(pin['lines'] for pin in manifest.values()) == lines
assert len(actual) == assertions
archive(owner,mode + '-scope-plan')
archive(peer,mode + '-scope-audit')
save('root-' + mode + '-scope-gate.json', {
    'status':'ACCEPTED_SOURCE_ONLY_' + mode.upper() + '_SCOPE', 'module':NAME,
    'root_complete_basis_and_scope_maps_read':True,
    'root_all_basis_AST_assertions_correlate':True,
    'basis_lines':lines,'basis_assertions':assertions,
    'selected_target':lines,'selected_hard_stop':hard,
    'literal_and_actual_data_adapters_only':True,
    'all_generic_guards_and_full_scope_retained':True,
    'independent_review_sha256':peer_review,
    'selected_authoring_authorized':True,
    'selected_activation_authorized':False,
    'future_proof_documents_seal_and_push_not_claimed':True,
    'goal_status':'ACTIVE_INCOMPLETE'})
print('PASS: ' + mode + ' source-only scope accepted; selected authoring only.')
