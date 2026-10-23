import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

source = Path('/tmp/mcfta-completed-hit-readback-signature')
audit = Path('/tmp/mcfta-completed-hit-readback-signature-audit')
pins = checked_package(source, 'd8c0477083c721b10f4cf6b93830ca75f41bce4783c73d981e62bff1d2fd663f',
    '75294b582cac3679fd0bdc612a9a4d2719bdcf7926773f78c202c7b7a96da445')
assert len(pins) == 57
contracts = load(source / 'contracts.json')
expected_names = ['context.lean.txt', 'private-yielded-done.lean.txt', 'private-ret-checked.lean.txt',
    'public-header.lean.txt', 'local-reverse-present.lean.txt', 'local-swap.lean.txt',
    'local-bindings.lean.txt', 'local-allocated.lean.txt', 'local-current-reverse.lean.txt',
    'local-current-stored.lean.txt']
assert list(contracts) == expected_names
assert sha(source / 'contracts.json') == '2008ff8495d37ab8c5bc42fd1b231895c4f9d4f9c6ce82942273ccb90188cdaf'
insertion = load(source / 'insertion-map.json')['compiled_fragments']
assert [item['file'] for item in insertion] == expected_names
assert [item['order'] for item in insertion] == list(range(1,11))
assert [item['lines'] for item in insertion] == [11,6,4,12,2,1,5,1,2,1]
for item in insertion:
    path = source / item['file']
    assert sha(path) == contracts[item['file']] == item['sha256']
    assert len(path.read_bytes().splitlines()) == item['lines']
shape = load(source / 'declaration-schema.json')
local_names = ['reversePresent','swap','allocated','currentReverse','currentStored']
assert shape['all_have_names_including_inferred'] == local_names
assert shape['all_let_names_including_inferred'] == ['published','current']
assert shape['private_helpers'] == ['yielded_done','ret_checked']
assert shape['new_global_definitions'] == shape['typed_show_fragments'] == []
assert shape['additional_typed_obtain_or_local_property'] == [] and shape['public_local_induction'] is None
assert shape['namespace'] == 'MicroCFTA.' + NAME
assert shape['public_heads'] == ['MicroCFTA.' + NAME + '.completed_hit_checked']
induction = shape['helper_induction']
assert induction['helper'] == 'ret_checked' and induction['inducted'] == 'pending : List Nat'
assert induction['generalized'] == ['fuel : Nat','before : Wrapper width']
assert induction['fixed'] == ['value : Edge','result : Edge','after : Wrapper width']
assert sha(source / induction['generated_IH_file']) == induction['generated_IH_sha256']
assert induction['generated_IH_repeated_as_typed_local_in_source'] is False
assert load(source / 'budget.json')['whole_source_hard_stop'] == shape['whole_source_hard_limit'] == 180
index = load(source / 'source-index.json')
assert len(index['sources']) == 11
cuts = lines = 0
for item in index['sources']:
    path = ROOT / item['path']
    data = path.read_bytes()
    assert data == (source / item['snapshot']).read_bytes()
    assert sha(path) == item['sha256'] and len(data) == item['bytes']
    assert len(data.splitlines()) == item['lines']
    for cut in item['cuts']:
        snapshot = source / cut['snapshot']
        assert snapshot.read_bytes() == b''.join(data.splitlines(True)[cut['start']-1:cut['end']])
        assert sha(snapshot) == cut['sha256'] and snapshot.stat().st_size == cut['bytes']
        cuts += 1
        lines += cut['end'] - cut['start'] + 1
assert (cuts, lines) == (18,392)
imports = load(source / 'import-closure.json')
assert imports['root_import'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeStable'
assert len(imports['modules']) == imports['project_modules'] == 1064
by_name = {item['module']: item for item in imports['modules']}
assert len(by_name) == 1064
for item in imports['modules']:
    path = ROOT / item['path']
    assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes']
    actual = re.findall(r'^import ([^\s]+)', path.read_text(), re.M)
    assert actual == item['imports'], item['module']
    assert all(child in by_name for child in actual if child.startswith('MicroCFTA.'))
for destination, route in imports['public_API_paths'].items():
    assert route[0] == imports['root_import'] and route[-1] == destination
    for first, second in zip(route,route[1:]):
        assert second in by_name[first]['imports']
reachable = set()
todo = [imports['root_import']]
while todo:
    name = todo.pop()
    if name not in reachable:
        reachable.add(name)
        todo.extend(child for child in by_name[name]['imports'] if child in by_name)
assert reachable == set(by_name)
assert 'import ' + imports['root_import'] in (source / 'context.lean.txt').read_text().splitlines()
assert imports['Ready_source_is_guide_not_imported'] is True
assert git('rev-parse','HEAD').strip() == START
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
independent = load(audit / 'review.json')
assert independent['status'] == 'SOURCE_ONLY_EXACT_DECLARATION_CLEAR'
assert independent.get('findings',[]) == []
archive(source, 'signature-plan')
archive(audit, 'signature-audit')
normalized_contracts = [dict(path=item['file'], lines=item['lines'], sha256=item['sha256']) for item in insertion]
report = dict(status='ROOT_DECLARATION_REVIEW_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    module='MicroCFTA.' + NAME, public_names=['completed_hit_checked'], private_names=['yielded_done','ret_checked'],
    local_names=local_names, local_let_names=['published','current'], local_induction=induction,
    typed_show_fragments=[], source_target=[135,165], source_hard_stop=180,
    contract_sha256=sha(source / 'contracts.json'), contracts=normalized_contracts,
    signature_contract_schema='filename to SHA string; order/roles/lines from insertion-map compiled_fragments',
    root_whole_exact_declarations_read=True, root_source_identities=11,
    root_source_cuts=cuts, root_source_cut_lines=lines, root_import_closure_modules=1064,
    root_import_paths_verified=True, generated_IH_reviewed=True,
    same_supplied_done_result_and_full_after_required=True, arbitrary_completed_fuel=True,
    genuine_initial_stable_and_published_key=True, only_checked_state_equality=True,
    second_completion_or_crossfuel_uniqueness=False, new_resources=False, admission_output=False,
    independent_source_review='CLEAR', independent_review_sha256=sha(audit / 'review.json'),
    body_proposal_authorized=True, compiler_authorized=False, whole_goal_complete=False)
save('root-declaration-review.json',report)
save('declaration-owner-harness-observation.json',dict(kind='PROVIDER_CAPACITY_INTERRUPTION_NOT_PROOF_JOB',
    observed_by_root_at='2026-10-23 04:56 CEST', original_harness_result='Selected model is at capacity. Please try a different model.',
    recovery='Same existing owner resumed, revalidated all frozen pins/source identities read-only, and reported FINAL.',
    frozen_source_rewritten=False, new_lean_lake_jobs=0, root_capped_metadata_failure=False))
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Exact declaration gate\n\nRoot and independent reviews accept all 10 exact compiled fragments and the generated IH.\nAll 11 defining sources, 18 cuts and 1064 import identities match.\nThe completed_hit_checked body proposal may use only the two reviewed private helpers.\nThe five local haves, two literal lets and exact ret_checked list induction stay fixed.\nThe SAME supplied done equation must give only checked-state equality.\nThe whole source has a 180-line hard stop. No compiler is authorized at this gate.\n')
print(json.dumps(report))
