exec(compile(open('/tmp/mcfta-scan-node-counter-growth-root-common.py').read(), '/tmp/mcfta-scan-node-counter-growth-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-after-pair-counter-investigation')
peer = Path(sys.argv[1])
checked_package(owner,'02b96f8bec8fa0cd794f798e8f4d1a3335d73cf54cdcae641ccc52261969ebcb','0f8f238b398cbcda09830c0d63c555a9f725af907126efc3e448024cb19d16e1')
checked_package(peer,sys.argv[2],sys.argv[3])
assert sha(peer / 'review.json') == sys.argv[4] and load(peer / 'review.json')['status'] == 'CLEAR'
sources = load(owner / 'source-index.json')['sources']
assert len(sources) == 5
for item in sources:
    relative = Path(item['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    raw = (ROOT / relative).read_bytes()
    assert raw == (owner / item['snapshot']).read_bytes()
    assert sha(ROOT / relative) == item['sha256'] and len(raw) == item['bytes']
    assert len(raw.splitlines()) == item['lines']
cuts = load(owner / 'cuts-index.json')
assert cuts['count'] == len(cuts['cuts']) == 12 and cuts['total_lines'] == 348
for item in cuts['cuts']:
    raw = b''.join((ROOT / item['source']).read_bytes().splitlines(keepends=True)[item['first_line']-1:item['last_line']])
    assert raw == (owner / item['path']).read_bytes() and len(raw.splitlines()) == item['lines']
    assert sha(owner / item['path']) == item['sha256'] and len(raw) == item['bytes']
routes = load(owner / 'import-routes.json')
for item in routes['existing_read_source_import_paths']:
    assert ('import '+item['module']) in (ROOT / item['from']).read_text().splitlines()
    assert (ROOT / item['resolved_path']).is_file()
assert load(owner / 'budget.json')['target'] == [85,115]
assert load(owner / 'budget.json')['proposed_hard_stop'] == 140
assert load(owner / 'inventory-plan.json')['private_helpers'] == []
archive(owner,'after-pair-counter-investigation')
archive(peer,'investigation-audit')
save('root-investigation-review.json',dict(status='ACCEPTED_PUBLIC_API_INVESTIGATION_ONLY',module=NAME,
    root_complete_note_plain_contract_inventory_budget_import_routes_and_12_cuts_348_lines_read=True,
    root_complete_Scan129_and_H37proof96_read_and_hashes_checked=True,full_source_hashes_checked=5,
    same_actual_full_pair_state_and_checked_native_heap_counter=True,all_five_outcomes=True,
    public_heads=[['outcomeState','def'],['step_mono','theorem'],['execute_mono','theorem']],
    accessor_requires_no_equality_instances=True,no_validity_readiness_success_or_counter_premise=True,
    no_private_helper_predicate_packet_ID_split_or_resume=True,source_target=[85,115],whole_source_hard_stop=140,
    below_target_without_padding_allowed=True,structural_growth_does_not_order_counters=True,
    exact_declaration_authoring_authorized=True,no_body_or_compiler_authorized=True,
    independent_review_sha256=sha(peer / 'review.json'),goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the source-only Scan counter investigation. Exact declaration review is required before any proof body.')
