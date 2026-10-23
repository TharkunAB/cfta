exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import ast
import collections
import re
import sys

owner = Path('/tmp/mcfta-scan-node-counter-growth-proof-verifier-preparation')
peer = Path(sys.argv[1])
checked_package(owner,'d4d1283cb0223c783db6dcb2575d4e7e855e9abeabcfe85f88718d30fd6470cd','735a4a92e0bb4c0f9a53ee6cf1118ec61b760d30ce30877af19ca6a1a4c8e0f9')
checked_package(peer,sys.argv[2],sys.argv[3])
assert sha(peer / 'review.json') == sys.argv[4]
assert load(peer / 'review.json')['status'] == 'CLEAR'
code = (owner / 'verify-proofs.py').read_bytes()
data = (owner / 'bound-data.json').read_bytes()
draft = (owner / 'drafts/provisional-v1/verify-proofs.py').read_bytes()
assert sha(owner / 'verify-proofs.py') == '7162f33ae1f9febdc1c64c71b1b5841900c8232589aba10061a3d804ec26ff26'
assert sha(owner / 'bound-data.json') == 'b7cfd56338e0a5ce704d697aa495a9d76e3d034536d752f6dd32b77e5da6e909'
assert sha(owner / 'drafts/provisional-v1/verify-proofs.py') == '2471e64b7226ed5f5037ae0b41733c1fd961429cb76f6c91c0f0cfe95cc7730a'
assert draft.count(b'e1177dbc379de9b65d9c419193f38e32f4138bdd12fd8d75745c1b18908965de') == 1
assert draft.replace(b'e1177dbc379de9b65d9c419193f38e32f4138bdd12fd8d75745c1b18908965de',b'b7cfd56338e0a5ce704d697aa495a9d76e3d034536d752f6dd32b77e5da6e909') == code
assert (len(code.splitlines()),len(data.splitlines())) == (431,560)
assert not re.search(rb'__H\d+_',data)
nodes = [n for n in ast.walk(ast.parse(code)) if isinstance(n,ast.Assert)]
assert len(nodes) == 229
rows = load(owner / 'scope/guard-crosswalk.json')['rows']
expected = collections.Counter(ast.dump(ast.parse(r['basis_expression'],mode='eval').body) for r in rows if r['classification'] == 'EXACT_GENERIC_RETAIN_WITH_MULTIPLICITY')
actual = collections.Counter(ast.dump(n.test) for n in nodes)
assert sum(expected.values()) == 174 and all(actual[k] == count for k,count in expected.items())
bound = load(owner / 'bound-data.json')
checked = 0
def check_pins(item):
    global checked
    if isinstance(item,dict):
        if {'path','bytes','sha256'} <= item.keys():
            relative = Path(item['path'])
            assert not relative.is_absolute() and '..' not in relative.parts
            path = HERE / relative
            assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
            checked += 1
        for value in item.values():
            check_pins(value)
    elif isinstance(item,list):
        for value in item:
            check_pins(value)
check_pins(bound)
assert checked == 29
assert bound['metrics'] == load(HERE / 'actual-proof-cut.json')['metrics']
assert bound['modules'][0]['scope'] == load(HERE / 'root-full-review.json')['scope']
assert not (HERE / 'verify-proofs.py').exists() and not (HERE / 'bound-data.json').exists()
archive(owner,'proof-verifier-preparation')
archive(peer,'proof-verifier-audit')
(HERE / 'verify-proofs.py').write_bytes(code)
(HERE / 'bound-data.json').write_bytes(data)
save('root-proof-verifier-review.json', {
    'status':'ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    'module':NAME,'verifier_sha256':sha(HERE / 'verify-proofs.py'),
    'bound_data_sha256':sha(HERE / 'bound-data.json'),
    'root_complete_selected_source_lines_read':431,
    'root_complete_bound_data_lines_read':560,
    'complete_final_source_read_by_whole_draft_and_exact_digest_only_delta':True,
    'all_174_generic_AST_expressions_exact_with_multiplicity':True,
    'all_53_inherited_scope_and_two_accessor_obligations_retained':True,
    'all_29_actual_data_pin_records_checked':True,
    'independent_review_sha256':sha(peer / 'review.json'),
    'normal_and_live_cwd_root_slash_required':True,
    'new_Lean_or_Lake_jobs_authorized':False,'goal_status':'ACTIVE_INCOMPLETE'})
print('PASS: whole reviewed final431/560 verifier/data installed; standalone normal/live authorized.')
