import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

source = Path('/tmp/mcfta-both-miss-native-covered-signature')
audit = Path('/tmp/mcfta-both-miss-native-covered-signature-audit')
pins = checked_package(source,
    'c1efe44cac1e127b4c7449d0d60363aeb0831f822632656f1ea122f84824ed4a',
    'e9fb0636ca0e5ccce41f4f9306d5c534a38685273ce4ed92f18f6c12cfbd9b77')
assert len(pins) == 81
contracts = load(source / 'contracts.json')
expected_names = ['context.lean.txt', 'public-header.lean.txt', 'local-bindings.lean.txt',
    'local-raw-scope.lean.txt', 'local-raw-covered.lean.txt', 'local-ordered-inputs.lean.txt',
    'local-ready.lean.txt', 'local-fields.lean.txt', 'local-certificate.lean.txt', 'local-final-covered.lean.txt']
assert list(contracts) == expected_names
assert sha(source / 'contracts.json') == 'a15bceac4e3d0f9d00532775221fc1133e197c4e39f06f8df78bc83894c29627'
for filename, pin in contracts.items():
    item = source / filename
    assert sha(item) == pin['sha256'] and item.stat().st_size == pin['bytes']
    assert len(item.read_bytes().splitlines()) == pin['lines']
assert [contracts[name]['lines'] for name in expected_names] == [21, 67, 2, 1, 1, 1, 1, 1, 3, 1]
insertion = load(source / 'insertion-map.json')
assert [item['file'] for item in insertion] == expected_names
assert [item['insertion_order'] for item in insertion] == list(range(10))
for item in insertion:
    assert all(item[key] == contracts[item['file']][key] for key in ['lines', 'bytes', 'sha256'])
shape = load(source / 'local-declaration-scope.json')
local_names = ['rawScope', 'rawCovered', 'orderedInputs', 'ready', 'fields', 'certificate', 'finalCovered']
assert shape['local_have_names'] == local_names
assert shape['local_let_names'] == ['ordered', 'request']
assert shape['private_helpers'] == shape['new_global_definitions'] == []
assert shape['typed_show_fragments'] == shape['local_IH_fragments'] == []
assert load(source / 'route-and-budget.json')['hard_stop_total_ordinary_source_lines'] == 180
index = load(source / 'source-index.json')
assert len(index['sources']) == 22
cuts = lines = 0
for item in index['sources']:
    live = ROOT / item['path']
    data = live.read_bytes()
    assert data == (source / item['snapshot']).read_bytes()
    assert sha(live) == item['sha256'] and len(data) == item['bytes']
    assert len(data.splitlines()) == item['lines']
    for cut in item['cuts']:
        snapshot = source / cut['snapshot']
        assert snapshot.read_bytes() == b''.join(data.splitlines(True)[cut['start']-1:cut['end']])
        assert sha(snapshot) == cut['sha256'] and snapshot.stat().st_size == cut['bytes']
        cuts += 1
        lines += cut['end'] - cut['start'] + 1
assert (cuts, lines) == (26, 471)
imports = load(source / 'public-import-routes.json')
def module_path(module):
    assert module.startswith('MicroCFTA.')
    return ROOT / 'lean' / (module.replace('.', '/') + '.lean')
context = (source / 'context.lean.txt').read_text()
for route in imports['routes'].values():
    assert route[0] in imports['context_roots']
    assert 'import ' + route[0] in context.splitlines()
    for first, second in zip(route, route[1:]):
        assert 'import ' + second in module_path(first).read_text().splitlines()
for item in imports['defining_source_import_pins'].values():
    path = ROOT / item['path']
    assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes']
    actual_lines = path.read_text().splitlines()
    for line in item['import_lines']:
        assert actual_lines[line['line'] - 1] == line['text']
original = (source / 'original-H13-public-header.lean.txt').read_text()
live = (ROOT / 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeOriginalRows.lean').read_text()
actual_header = 'theorem both_miss_complete' + live.split('theorem both_miss_complete', 1)[1].split(' := by', 1)[0] + '\n'
assert original == actual_header
specialized = original
operations = load(source / 'H13-specialization.json')['operations']
assert len(operations) == 9
for operation in operations:
    assert specialized.count(operation['before']) == 1
    specialized = specialized.replace(operation['before'], operation['after'], 1)
public = (source / 'public-header.lean.txt').read_text()
assert public.split('\n', 1)[1] == specialized
for operation in reversed(operations):
    assert specialized.count(operation['after']) == 1
    specialized = specialized.replace(operation['after'], operation['before'], 1)
assert specialized == original
assert git('rev-parse', 'HEAD').strip() == START
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
independent = load(audit / 'review.json')
assert independent['status'] == 'SOURCE_ONLY_EXACT_DECLARATION_CLEAR' and independent['findings'] == []
archive(source, 'signature-plan')
archive(audit, 'signature-audit')
report = dict(status='ROOT_DECLARATION_REVIEW_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    module='MicroCFTA.' + NAME, public_names=['both_miss_complete'], private_names=[],
    local_names=local_names, local_let_names=['ordered', 'request'], local_induction=None,
    typed_show_fragments=[], source_target=[140, 170], source_hard_stop=180,
    contract_sha256=sha(source / 'contracts.json'),
    contracts=[dict(path=filename, lines=pin['lines'], sha256=pin['sha256']) for filename, pin in contracts.items()],
    root_whole_exact_declarations_read=True, root_source_identities=22,
    root_source_cuts=cuts, root_source_cut_lines=lines, root_import_paths_verified=True,
    exact_H13_header_inverse=True, same_H13_witness_and_full_after_required=True,
    same_native_receipt_trace_required=True, finite_model_and_ranked_fixed=True,
    genuine_parent_admission_and_initial_covered_explicit=True, only_native_covered_appended=True,
    new_success_or_final_certificate_premise=False, new_resources=False, pair_admission_output=False,
    independent_source_review='CLEAR', independent_review_sha256=sha(audit / 'review.json'),
    body_proposal_authorized=True, compiler_authorized=False, whole_goal_complete=False)
save('root-declaration-review.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Exact declaration gate\n\nRoot and independent reviews accept all10 exact ordered contracts.\nThe exact H13 header inverse and all22 source identities/26 public cuts pass.\nOne both_miss_complete body proposal is authorized with the seven reviewed local facts.\nThe two literal bindings stay fixed. No helper, typed show or induction is authorized.\nThe same H13 witness and native Receipt.trace must derive final Covered.\nThe whole source has a180-line hard stop. No compiler is authorized at this gate.\n')
print(json.dumps(report))
