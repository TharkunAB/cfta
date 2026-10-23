exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-scan-node-counter-growth-source-history-scope-plan')
peer = Path('/tmp/mcfta-scan-node-counter-growth-source-history-scope-review')
checked_package(owner, 'f519706542f1f8ca6f2c212b5eaa52ae93412b910a35e15794f22c71908ba7a9', 'b26743805d30393d4c67e255016b9b5ae57b3c85774eb08861487d9004e5eb5b')
checked_package(peer, '468d91e8be125a7287b261befbedc866b6028fb66ecb405c9d7c673fc25c6461', '8f3467f981e5462551f99b143262078089795c8fd7ad4f597d22be1e3b996d74')
assert sha(peer / 'review.json') == 'a62f1dd229563f4f92c651ecb94e341611a96614b5d6357e70e7a38394a53191'
assert load(peer / 'review.json')['status'] == 'CLEAR'
basis = (owner / 'basis/source-history.py').read_text()
assert len(basis.splitlines()) == 78
guards = sorted((n for n in ast.walk(ast.parse(basis)) if isinstance(n, ast.Assert)), key=lambda n:n.lineno)
assert len(guards) == 14
assert [(r['line'], r['expression']) for r in load(owner / 'guard-crosswalk.json')] == [(n.lineno, ast.unparse(n.test)) for n in guards]
assert sha(owner / 'known-inputs/root-common.py') == sha(HERE / 'root-common.py')
archive(owner, 'source-history-scope-plan')
archive(peer, 'source-history-scope-audit')
save('root-source-history-scope-gate.json', {
    'status':'ACCEPTED_SOURCE_ONLY_HISTORY_COLLECTOR_SCOPE', 'module':NAME,
    'root_complete_26_line_plan_78_line_basis_both_46_line_common_and_14_guards_read':True,
    'selected_target':78, 'selected_hard_stop':90,
    'literal_substitutions_only':True,
    'all_generic_guards_and_dynamic_inventories_retained':True,
    'known_failed_metadata_attempt_and_corrected_retry_retained':True,
    'actual_variant_staged':False,
    'actual_FULL_and_Audit_required_before_execution':True,
    'independent_review_sha256':sha(peer / 'review.json'),
    'selected_authoring_authorized':True, 'selected_activation_authorized':False,
    'counts_and_artifacts_remain_dynamic':True})
print('PASS: independent source-history scope accepted; selected authoring only.')
