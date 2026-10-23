exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast
from collections import Counter
owner = Path('/tmp/mcfta-pair-node-counter-growth-proof-verifier-preparation')
peer = Path('/tmp/mcfta-pair-node-counter-growth-proof-verifier-audit')
checked_package(owner,'dd78ade246473a93da66e9315ab41d5034f5f772e4f06454b7617d2b2726a7cc','42ea8eeb906755c6844c6aaf3bf160954b1feb214ee3486ea4265d57cca685bb')
checked_package(peer,'71e91f6a132f9011ab5eae25e6eaad6308d33e3c8e83cb72759931dc9b380298','9d96b44f11218bd001cd4b5627f3bd1276619bd3522c7f159e5e9dd526832671')
assert sha(peer / 'review.json') == '029a85e7d43c27fd097611c5217cc17e995ba82c59f4e63ee2230a83cdf00775'
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and not review['blockers']
code = (owner / 'verify-proofs.py').read_bytes()
data = (owner / 'bound-data.json').read_bytes()
assert sha(owner / 'verify-proofs.py') == '9c6b2e7e537f8e5b04ba45bb9acdd8342cee905ae2d00871a3c94f6dd621c79f'
assert sha(owner / 'bound-data.json') == '1e12cb608db0a52a00d4e4838d72777a2ee3607e34a15d13904fcc83b4174985'
assert len(code.splitlines()) == 428 and len(data.splitlines()) == 583
draft = owner / 'drafts/01-pending-verify-proofs.py.txt'
assert sha(draft) == '252aea4e9d30a1d67355b1ff9337c8bbb5cab727d4bba08baa3d20e5b03af52c'
assert draft.read_bytes().replace(b'__H37_BOUND_DATA_SHA256__',sha(owner / 'bound-data.json').encode()) == code
assert sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(code))) == 227
inventory = load(owner / 'selected-assertion-inventory.json')
generic = Counter(row['expression'] for row in inventory['rows'] if row['classification'] == 'EXACT_INHERITED_GENERIC')
assert sum(generic.values()) == 174
for source in [code,(ROOT / 'lean/restart-evidence/20261023-demand-node-counter-growth/verify-proofs.py').read_bytes()]:
    expressions = Counter(ast.unparse(node.test) for node in ast.walk(ast.parse(source)) if isinstance(node,ast.Assert))
    assert all(expressions[text] == count for text,count in generic.items())
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
archive(owner,'proof-verifier-preparation')
archive(peer,'proof-verifier-audit')
for name in ['verify-proofs.py','bound-data.json']:
    assert not (HERE / name).exists()
    (HERE / name).write_bytes((owner / name).read_bytes())
save('root-proof-verifier-review.json',dict(status='ACCEPTED_WHOLE_REVIEWED_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(HERE / 'verify-proofs.py'),bound_data_sha256=sha(HERE / 'bound-data.json'),
    independent_review_sha256=sha(peer / 'review.json'),root_complete_selected_code_lines_read=428,
    root_complete_bound_data_lines_read=583,root_complete_basis_lines_read=424,
    root_draft_plus_exact_actual_data_digest_delta_read=True,all_generic_174_assertions_exact=True,
    all_50_scope_adapters_and_three_accessor_guards_reviewed=True,whole_source_hard_stop=450,
    actual_assertions=227,no_extra_proof_job=True,actual_public_TYPE_raw_booleans=[False,True,True],
    full_generalized_IH_and_fourteen_equation_types_retained=True,
    external_qualified_native_dependency_only_token_view_guarded=True,
    external_dependency_requires_exact_reviewed_command_line=True,
    all_drafts_and_reviewer_diagnostics_retained=True,
    standalone_normal_and_live_from_cwd_slash_authorized=True,
    proof_commit_and_document_write_require_both_actual_mode_PASS=True,goal_status='ACTIVE_INCOMPLETE'))
print('Accepted and installed the complete actual saved-proof verifier and bound data.')
