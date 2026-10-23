exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import ast
import difflib

audit = Path('/tmp/mcfta-fresh-node-counter-growth-source-history-audit')
checked_package(audit, '114b1849c2996416efa94e0f51d005428be3a27025b39f266127ac89d7f282c1', '77c3803a08fb9334e4153c2569e14a47bc2ea68f5b68d40c30e7db58cf103dc9')
assert sha(audit / 'review.json') == '2c7582675187f66fad782f9c2d98be22a8b8dc97fcfcdeeaf2823a4f6c96b33e'
assert load(audit / 'review.json')['status'] == 'CLEAR'
history = HERE / 'source-history-gate.json'
assert sha(history) == 'e57b389eea481bc2fc1465b45bf3bf6d65c60cf64ac976ba3c0fac74ff84183d'
assert sha(HERE / 'actual-proof-cut.json') == 'e3c7ca2f7b255c737340dc8a3e4c9b598aad712e87b4058e4e38a4d4c9d8b315'
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == '2ce7e811918f8dbf189bd9d1ea4cc2a9bef35d80f42dc9b750f998b68b866ca8'
cut = load(HERE / 'actual-proof-cut.json')
assert cut['metrics'] == dict(actual_jobs=5, source_jobs=4, focused_build_jobs=0, audit_jobs=1, failed_jobs=1, warned_source_exit_zero_jobs=1, rejected_public_type_jobs=0)
assert cut['artifacts'] == 2283 and cut['variants'] == 4 and cut['patches'] == 3
assert cut['metadata_jobs'] == 23 and cut['failed_metadata_jobs'] == 1
assert cut['audit']['build_jobs'] == 3652 and cut['audit']['dependencies'] == 75541
archive(audit, 'source-history-audit')
save('root-source-history-review.json', dict(status='ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY',
    root_whole_selected_source_lines_read=117, root_all_complete_public_TYPEs_read=True,
    source_history_sha256=sha(history), independent_review_sha256=sha(audit / 'review.json'),
    **cut['metrics'], variants=4, patches=3, artifacts=2283,
    root_metadata_cut_jobs=23, failed_root_metadata_jobs=1,
    complete_nested_control_coverage=True, Audit_one_import_inverse=True,
    original_schema_cut_and_label_repair_retained=True, generic_diff_guard_unchanged=True,
    goal_status='ACTIVE_INCOMPLETE'))
owner = Path('/tmp/mcfta-fresh-node-counter-growth-closing-tool-source')
review = Path('/tmp/mcfta-fresh-node-counter-growth-closing-source-audit')
checked_package(owner, '9520875fbf350b0870dec1d03dd4354893aae4502dff57c840dd85be4894c70f', '979557d2e7cffef10e53ee780bd8244fc9fc37aafed392005d5c9ca035297994')
checked_package(review, '52d9fe0944bcbda0fb92723ab8afe159ca022162326aa828812eb227eb49c633', 'dc597937355b969232e5b9b94044c9c864ce4e65f8fccb81234d8e71b573a2ca')
assert sha(review / 'review.json') == '84775c5af6d0011766737a8197c300f76855592b7d01101bd2d2f59b9fbc459b'
assert load(review / 'review.json')['status'] == 'CLEAR'
recipes = load(owner / 'literal-bindings.json')['files']
line_count = assertion_count = 0
for name, replacements in recipes.items():
    basis = (owner / 'basis' / (name + '.txt')).read_text()
    selected = (owner / 'selected' / name).read_text()
    computed = basis
    for item in replacements:
        assert computed.count(item['before']) == item['occurrences_at_step']
        computed = computed.replace(item['before'], item['after'])
    assert computed == selected
    line_count += len(selected.splitlines())
    assertion_count += sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(selected)))
assert (line_count, assertion_count) == (236, 59)
archive(owner, 'closing-preparation')
archive(review, 'closing-source-audit')
installed = {}
for name in recipes:
    assert not (HERE / name).exists()
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
    installed[name] = sha(HERE / name)
assert installed['verify-seal.py'] == '66c31c1a9da922463cccc5cb4879a86255157f6b77d6b60d51788ab394ccd8a7'
save('root-closing-tools-review.json', dict(status='ACCEPTED_WHOLE_REVIEWED_FIVE_CLOSING_TOOLS',
    installed_tools=installed, root_whole_selected_lines_read=236,
    root_whole_basis_read_in_prior_checkpoint=True, exact_literal_recipes_reviewed=True,
    exact_forward_and_inverse_patches_reviewed=True, independent_review_sha256=sha(review / 'review.json'),
    no_guard_removed=True, support_collection_once=True, mandatory_seal_checkpoint_rerun=True,
    standalone_modes_before_proof_commit=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED source/history and installed five closing tools; selected programs not executed.')
