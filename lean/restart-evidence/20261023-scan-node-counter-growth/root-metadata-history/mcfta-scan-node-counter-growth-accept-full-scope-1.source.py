import ast
import datetime
import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location('common', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py')
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)
HERE, load, sha = common.HERE, common.load, common.sha
owner = Path('/tmp/mcfta-scan-node-counter-growth-full-scope-plan')
peer = Path('/tmp/mcfta-scan-node-counter-growth-full-scope-review')
common.checked_package(owner, 'd6d6e8c3b8981184613740da664480b33685df3c4750773b9d530474ac548f33', '3f251908c968f6f5e78f1293447a8ad9b24ef4aa799b6afe978b468b380709c3')
common.checked_package(peer, '87bf40179859e8d83d9fb0732fd5b2304393c22c67a8bc66f4fa6b109819a2b3', 'e449c70556a35bf77a97349a4e06864f133bbaf3722ee08892ad467848b13b77')
assert sha(peer / 'review.json') == 'cd5d5e22dfb10632423837c3735b3bf3af359cc4c921e97378312ede5161b678'
assert load(peer / 'review.json')['status'] == 'CLEAR'
basis = load(owner / 'basis-manifest.json')
assert (basis['total_lines'], basis['total_assertions'], basis['hard_stop']) == (213, 73, 230)
actual = []
for name, record in basis['sources'].items():
    p = owner / 'basis' / name
    assert sha(p) == record['sha256'] == sha(Path(record['active_path'])) == sha(Path(record['archived_path']))
    assert len(p.read_text().splitlines()) == record['lines']
    assertions = sorted((n for n in ast.walk(ast.parse(p.read_text())) if isinstance(n, ast.Assert)), key=lambda n:n.lineno)
    assert len(assertions) == record['assertions']
    actual += [(name, n.lineno, ast.unparse(n.test)) for n in assertions]
assert actual == [(r['file'], r['line'], r['complete_expression']) for r in load(owner / 'guard-crosswalk.json')['assertions']]
for rel, pin in load(owner / 'input-map.json')['known_actual_inputs'].items():
    assert sha(Path(pin['actual_path'])) == pin['sha256'] == sha(owner / 'known-inputs' / rel)
assert load(HERE / 'selected-source-gate.json')['source_sha256'] == '7db9cd645899e31a3f04149e0ea8bd27f8e5c55c336aab872f8c286c04822cb7'
assert len(load(owner / 'gate-field-adapters.json')['adapters']) == 10
assert common.git('rev-parse', 'HEAD').strip() == common.START
common.archive(owner, 'full-scope-plan')
common.archive(peer, 'full-scope-plan-audit')
common.save('root-full-tool-scope-gate.json', {
    'status':'ACCEPTED_SOURCE_ONLY_FULL_TOOL_SCOPE_BEFORE_SELECTED_AUTHORING',
    'module':common.NAME, 'basis_lines':213, 'basis_assertions':73,
    'target_lines':[213,220], 'hard_stop':230, 'no_padding':True,
    'root_whole_basis_and_all_73_assertions_read':True,
    'root_all_ten_actual_gate_field_adapters_and_all_input_maps_read':True,
    'all_73_AST_guard_expressions_verified':True,
    'independent_review_sha256':sha(peer / 'review.json'),
    'selected_tool_authoring_authorized':True,
    'activation_requires_whole_selected_source_review':True,
    'actual_strict_source_already_passed':True,
    'FULL_Audit_official_install_results_pending':True,
    'goal_status':'ACTIVE_INCOMPLETE'})
progress = HERE / 'current-progress.md'
with progress.open('a') as handle:
    handle.write('\nUpdate ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '.\n')
    handle.write('The unchanged 80-line source passed its first strict Lean check.\n')
    handle.write('Its SHA256 is 7db9cd645899e31a3f04149e0ea8bd27f8e5c55c336aab872f8c286c04822cb7.\n')
    handle.write('The strict log is empty. Default declaration limits and all linters apply.\n')
    handle.write('One proof compiler job passed. No mathematical source patch was required.\n')
    handle.write('Retain the failed next-consumer metadata reader attempt and its corrected passing attempt.\n')
    handle.write('That failure did not involve Lean or alter the mathematical source.\n')
    handle.write('Root accepted the independent FULL tool scope review. Selected tool source review is next.\n')
    handle.write('FULL, Audit, official installation, commits, seal and push remain pending.\n')
    handle.write('The source-only next-consumer route is accepted pending the H38 dependency.\n')
print('PASS: exact FULL scope, all73 AST guards, independent review and current strict source accepted.')
