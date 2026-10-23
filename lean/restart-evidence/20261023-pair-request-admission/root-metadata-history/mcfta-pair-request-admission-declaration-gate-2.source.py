import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

source = Path('/tmp/mcfta-pair-request-admission-signature')
audit = Path('/tmp/mcfta-pair-request-admission-signature-audit')
pins = checked_package(source,
    '0b3b97a55a33856400e3375212ff44119cae1db6ba1efacf8d3df9d45dff7944',
    'f09a845da5e1dc55c26e4bc596ac3d9d0606f3ad93c6e76d46b67c6d6384b144')
assert len(pins) == 42
index = load(source / 'source-index.json')
assert len(index['sources']) == 8
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
assert cuts == 15
imports = load(source / 'import-paths.json')
for item in imports['used_public_api_paths']:
    route = item['route']
    assert 'MicroCFTA.' + route[0] in imports['direct_imports']
    for first, second in zip(route, route[1:]):
        assert 'import MicroCFTA.' + second in (ROOT / 'lean/MicroCFTA' / (first + '.lean')).read_text().splitlines()
contracts = load(source / 'contracts.json')
assert list(contracts) == ['context.lean.txt', 'public-header.lean.txt', 'local-property.lean.txt',
    'local-swapped.lean.txt', 'local-initial.lean.txt', 'local-preserved.lean.txt', 'local-final.lean.txt']
assert sha(source / 'contracts.json') == '0d0cba9e4d31c3f512c3849609c898039703392837c284ef622567a8379d5fe3'
for filename, pin in contracts.items():
    item = source / filename
    assert sha(item) == pin['sha256'] and len(item.read_bytes().splitlines()) == pin['lines']
shape = load(source / 'declaration-shape.json')
assert shape['module'] == 'MicroCFTA.' + NAME
assert shape['public_declarations'] == [dict(kind='theorem', name='completed_admitted', header='public-header.lean.txt')]
assert shape['private_declarations'] == shape['new_global_definitions'] == []
assert [item['name'] for item in shape['local_fragments']] == ['property', 'swapped', 'initial', 'preserved', 'final']
assert shape['no_other_typed_local_declarations_or_induction_statements_planned']
assert load(source / 'budget.json')['hard_stop'] == 180
assert git('rev-parse', 'HEAD').strip() == START
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
checked_package(audit, sys.argv[1], sys.argv[2])
independent = load(audit / 'review.json')
assert independent['status'] == 'CLEAR' and independent['findings'] == []
assert sha(audit / 'review.json') == sys.argv[3]
archive(source, 'signature-plan')
archive(audit, 'signature-audit')
report = dict(status='ROOT_DECLARATION_REVIEW_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    module='MicroCFTA.' + NAME, public_names=['completed_admitted'], private_names=[],
    local_names=['property', 'swapped', 'initial', 'preserved', 'final'], local_induction='preserved',
    source_target=[90, 150], source_hard_stop=180, contract_sha256=sha(source / 'contracts.json'),
    contracts=[dict(path=filename, lines=pin['lines'], sha256=pin['sha256']) for filename, pin in contracts.items()],
    root_whole_exact_declarations_read=True, root_source_identities=8, root_source_cuts=cuts,
    root_source_cut_lines=lines, independent_source_review='CLEAR',
    independent_freeze_sha256=sha(audit / 'FROZEN.json'), independent_pins_sha256=sha(audit / 'pins.json'),
    same_observed_run_and_full_after_state=True, all_captured_cells_including_unreferenced=True,
    genuine_initial_and_current_admission_explicit=True, final_admission_derived=True,
    future_success_premise=False, new_result_law_premise=False, native_covered_claimed=False,
    body_proposal_authorized=True, compiler_authorized=False, whole_goal_complete=False)
save('root-declaration-review.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Exact declaration gate\n\nRoot and independent reviews pass for all seven exact fragments.\nOne completed_admitted body proposal is authorized.\nOnly the reviewed property and four typed local facts are permitted.\nThe preserved fact uses one generalized fuel/control induction.\nAll actual captured cells are included. Native coverage remains separate.\nThe source has a 180-line hard stop. No compiler command is authorized yet.\nThe whole goal remains ACTIVE.\n')
print(json.dumps(report))
