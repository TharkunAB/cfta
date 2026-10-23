exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-pair-node-counter-growth-source-history-scope-plan')
peer = Path('/tmp/mcfta-pair-node-counter-growth-source-history-scope-audit')
checked_package(owner,'34cc56467ac7dbf9012c51356c2d9f14fa5723d5d029ad6bee1ce40b939568ac','dbddf43e44553071ec79c0397dda668c99a778888664bad1d190fc8df7edb34f')
checked_package(peer,'effb6c70fcd23cd0ffd2ed3f7038d17edc0baa7bc902adb521f157b0d32a86c5','d23885ba87063340d3c1d42a4abd4d19d68d1a1a921eb16ee9b5524173c7c834')
assert sha(peer / 'review.json') == '0b991cdc06a78cac2ff0a913856f9ea655897234a2ecea3e926057e56343d3f8'
assert load(peer / 'review.json')['status'] == 'CLEAR'
basis = ROOT / 'lean/restart-evidence/20261023-demand-node-counter-growth/completed-root-support/mcfta-demand-node-counter-growth-source-history.py'
assert len(basis.read_bytes().splitlines()) == 78
assert sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(basis.read_text()))) == 14
variant = HERE / 'variants/v1' / (NAME + '.lean')
assert sha(variant) == '6cfaf5e340d26b8c838f51d93fb3ae0e03b098510ca41b5021ada4e96b72c2e8'
assert variant.read_bytes() == (HERE / (NAME + '.lean')).read_bytes()
assert load(HERE / 'root-cohort-audit-gate.json')['build_jobs'] == 3656
archive(owner,'source-history-scope-plan')
archive(peer,'source-history-scope-audit')
save('root-source-history-scope-gate.json',dict(status='ACCEPTED_SOURCE_ONLY_HISTORY_COLLECTOR_SCOPE',
    module=NAME, root_complete_26_line_plan_78_line_basis_46_line_common_and_14_guards_read=True,
    selected_target=78,selected_hard_stop=90,literal_substitutions_only=True,
    all_generic_guards_and_dynamic_inventories_retained=True,
    actual_variant_staged=True,metadata_corrections_separate_from_proof_history=True,
    independent_review_sha256=sha(peer / 'review.json'),selected_authoring_authorized=True,
    selected_activation_authorized=False,counts_and_artifacts_remain_dynamic=True))
print('Accepted the source-history collector scope. Complete selected review must precede execution.')
