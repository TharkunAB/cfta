exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-scan-node-counter-growth-source-history-preparation')
peer = Path('/tmp/mcfta-scan-node-counter-growth-source-history-tool-review')
checked_package(owner, '2ca71fdae149649d8a25ed1c08cf7aff5d693c5a70500069c76fad28f41d98e5', 'cb8d481a5dcecf4502d74e9abfa3259a0ed849c5c7c9318d15994c49961907dd')
checked_package(peer, '5739e9ed1362df9c249663e67abc712ced303ed275c9992b936911f71756f93a', 'b66b3357ae8437e0d2c2983648d0e6bdd7ac7da09630a21bd4d958ab59d50ce5')
assert sha(peer / 'review.json') == 'b3699119edaa8375e99b0ac24e69b24dcfbea73ca5a793aaf18fcbe28992324b'
assert load(peer / 'review.json')['status'] == 'CLEAR'
manifest = load(owner / 'selected-scripts.json')
for name, record in manifest.items():
    selected = owner / 'selected' / name
    assert sha(selected) == record['sha256'] and len(selected.read_text().splitlines()) == record['lines']
    assert sum(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(selected.read_text()))) == record['assertions']
    adapted = (owner / 'basis' / name).read_text()
    recipe = load(owner / 'literal-recipe.json')['recipes'][name]
    for change in recipe:
        assert adapted.count(change['from']) == change['occurrences']
        adapted = adapted.replace(change['from'],change['to'])
    assert adapted == selected.read_text()
    for change in reversed(recipe):
        assert adapted.count(change['to']) == change['occurrences']
        adapted = adapted.replace(change['to'],change['from'])
    assert adapted == (owner / 'basis' / name).read_text()
assert (owner / 'selected/root-common.py').read_bytes() == (HERE / 'root-common.py').read_bytes() == Path('/tmp/mcfta-scan-node-counter-growth-root-common.py').read_bytes()
assert load(HERE / 'root-cohort-audit-gate.json')['status'] == 'ACCEPTED_ACTUAL_AGGREGATE_AUDIT'
assert load(HERE / 'root-full-review.json')['status'] == 'ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED'
assert load(HERE / 'root-variant-staging.json')['body_strict_and_canonical_bytes_equal']
assert not (HERE / 'source-history.py').exists()
archive(owner, 'source-history-preparation')
archive(peer, 'source-history-tool-audit')
(HERE / 'source-history.py').write_bytes((owner / 'selected/source-history.py').read_bytes())
save('root-source-history-tool-gate.json', {
    'status':'ACCEPTED_EXACT_HISTORY_COLLECTOR_AND_CURRENT_COMMON', 'module':NAME,
    'root_complete_selected_collector_lines_read':78, 'root_complete_current_common_lines_read':46,
    'selected_assertions':14, 'common_assertions':7, 'selected_hard_stop':90,
    'installed_collector_sha256':sha(HERE / 'source-history.py'),
    'current_common_sha256':sha(HERE / 'root-common.py'),
    'independent_review_sha256':sha(peer / 'review.json'),
    'actual_FULL_Audit_and_variant_staging_checked':True,
    'complete_dynamic_metadata_failures_and_six_file_bundles_retained':True,
    'execution_authorized':True, 'actual_counts_remain_dynamic':True})
print('PASS: exact reviewed history collector installed after actual FULL, Audit and variant staging.')
