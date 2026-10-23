exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import ast
import sys

owner = Path('/tmp/mcfta-scan-node-counter-growth-full-preparation')
peer = Path('/tmp/mcfta-scan-node-counter-growth-full-tool-review')
checked_package(owner, 'a50825c974793bb92c7f65f77b2100ec81b13af0b6f08c2f194fa2809dc9e611', '4df939be2c6bc93d4251b1b88f254a7786b096aef168931e8b7baabf53fd37b7')
checked_package(peer, sys.argv[1], sys.argv[2])
assert sha(peer / 'review.json') == sys.argv[3]
assert load(peer / 'review.json')['status'] == 'CLEAR'
manifest = load(owner / 'selected-scripts.json')
recipes = load(owner / 'literal-recipe.json')['recipes']
for name, record in manifest.items():
    source = owner / 'selected' / name
    assert sha(source) == record['sha256']
    assert len(source.read_text().splitlines()) == record['lines']
    assert sum(isinstance(n, ast.Assert) for n in ast.walk(ast.parse(source.read_text()))) == record['assertions']
    adapted = (owner / 'basis' / name).read_text()
    for change in recipes[name]:
        assert adapted.count(change['from']) == change['occurrences']
        adapted = adapted.replace(change['from'], change['to'])
    assert adapted == source.read_text()
    for change in reversed(recipes[name]):
        assert adapted.count(change['to']) == change['occurrences']
        adapted = adapted.replace(change['to'], change['from'])
    assert adapted == (owner / 'basis' / name).read_text()
    assert not (HERE / name).exists()
assert sum(r['lines'] for r in manifest.values()) == 213
assert sum(r['assertions'] for r in manifest.values()) == 73
assert len((owner / 'diagnostic-tail.lean.txt').read_text().splitlines()) == 20
assert sha(HERE / 'root-body-v1.lean') == '7db9cd645899e31a3f04149e0ea8bd27f8e5c55c336aab872f8c286c04822cb7'
for suffix in ['.lean', '.full.lean']:
    assert not (HERE / (NAME + suffix)).exists()
assert not (HERE / 'actual-scan-node-counter-growth-headers.lean.txt').exists()
archive(owner, 'full-preparation')
archive(peer, 'full-preparation-audit')
for name in manifest:
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
save('root-full-tool-gate.json', {
    'status':'ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE', 'module':NAME,
    'source_sha256':sha(HERE / 'root-body-v1.lean'), 'source_lines':80,
    'selected_strict':'root-scan-node-counter-growth-strict-1',
    'public_heads':['outcomeState','step_mono','execute_mono'], 'private_helpers':[],
    'independent_review_sha256':sha(peer / 'review.json'),
    'root_complete_selected_lines_read':213, 'root_complete_basis_lines_read':213,
    'root_all_sources_and_exact_diffs_read':True,
    'selected_lines':213, 'selected_hard_stop':230, 'selected_assertions':73,
    'diagnostic_tail_lines':20, 'materializer_cli_arguments':7,
    'installed_tools':{name:record['sha256'] for name,record in manifest.items()},
    'materializer_activation':True, 'sole_FULL_activation':True,
    'reader_activation_after_actual_FULL':True,
    'all_generic_guard_families_preserved':True,
    'canonical_nonoverwrite_guard_retained':True,
    'canonical_evidence_source_absent_before_materializer':True,
    'goal_status':'ACTIVE_INCOMPLETE'})
print('PASS: exact reviewed FULL tools installed; one materialization/FULL authorized.')
