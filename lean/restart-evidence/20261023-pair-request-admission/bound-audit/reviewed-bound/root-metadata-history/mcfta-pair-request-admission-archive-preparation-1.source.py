import ast
import datetime
import difflib
import runpy
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

source = Path('/tmp/mcfta-pair-request-admission-prepared-tools')
previous = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
pins = checked_package(source,
    'bb23e85716be30f686765c6391cf6e331a8d6ca3356b71953f9b78eb258a8a26',
    '38d64b3505a88cddba07cb16f43f71dd295dcb053e83e047254351205a0563fb')
assert len(pins) == 88
selected = load(source / 'selected-scripts.json')
scripts = selected['scripts']
assert len(scripts) == 12
lines = assertions = 0
for filename, pin in scripts.items():
    path = source / filename
    assert sha(path) == pin['sha256'] and path.stat().st_size == pin['bytes']
    assert len(path.read_bytes().splitlines()) == pin['lines']
    tree = ast.parse(path.read_bytes())
    assert sum(isinstance(node, ast.Assert) for node in ast.walk(tree)) == pin['ast_assertions']
    predecessor = source / pin['predecessor']
    assert predecessor.read_bytes() == (previous / filename).read_bytes()
    lines += pin['lines']
    assertions += pin['ast_assertions']
assert lines == 1024 and assertions == 332
assert (source / 'root-run-check.py').read_bytes() == (previous / 'root-run-check.py').read_bytes()
assert (source / 'verify-seal.py').read_bytes() == (previous / 'verify-seal.py').read_bytes()
assert (source / 'signature-proposal/root-declaration-review.json').read_bytes() == (HERE / 'root-declaration-review.json').read_bytes()
archive(source, 'checkpoint-preparation')
report = dict(status='ROOT_WHOLE_TOOL_SOURCE_CLEAR_PENDING_INDEPENDENT_GATE',
    observed_at=datetime.datetime.now().astimezone().isoformat(), scripts=12,
    lines=lines, assertions=assertions, pins_verified=len(pins), complete_selected_source_read=True,
    exact_seven_contract_shape_delta_read=True, inherited_binding_values_retained_programmatically=True,
    runner_and_seal_verifier_unchanged=True, independent_preparation_review='PENDING',
    prepared_execution_authorized=False, compiler_authorized=False, new_proof_jobs=0)
save('root-preparation-read-scope.json', report)
print(json.dumps(report))
