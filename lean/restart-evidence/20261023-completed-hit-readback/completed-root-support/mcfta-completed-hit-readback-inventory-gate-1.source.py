import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

source = Path('/tmp/mcfta-completed-hit-readback-next-inventory')
audit = Path('/tmp/mcfta-completed-hit-readback-next-inventory-audit')
pins = checked_package(source,
    '6091bafc2b9193e5c42a01db5ac9878a0cdd5000cfa0f5396e8450bea3028ee1',
    '5cce5cac093d748892741c5219e98979380a50957b4120e85f414fa4d05668e7')
assert len(pins) == 96
assert sha(source / 'source-index.json') == '6fe20517084cd865291139a9aa01dad50b2b3aa1e61ea8ab775c276d21ce2610'
index = load(source / 'source-index.json')
assert len(index['sources']) == 28
cuts = lines = 0
for item in index['sources']:
    live = Path(item['path'])
    assert live.is_relative_to(ROOT / 'lean/MicroCFTA')
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
assert (cuts, lines) == (34, 596)
assert load(HERE / 'root-full-review.json')['status'] == 'ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT'
assert load(HERE / 'completed-hit-readback-audit-1.json')['exit_code'] == 0
assert sha(HERE / 'completed-hit-readback-audit-1.log') == '29318583ac1dc0be2b57a786bd01643bee63c16c849f5bc9f199cf5bcd513376'
addition = ('import MicroCFTA.' + NAME + '\n').encode()
aggregate = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert aggregate.count(addition) == 1
assert aggregate.replace(addition, b'', 1) == (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
checked_package(audit, sys.argv[1], sys.argv[2])
independent = load(audit / 'review.json')
assert independent['status'] == 'CLEAR' and sha(audit / 'review.json') == sys.argv[3]
archive(source, 'next-inventory')
archive(audit, 'next-inventory-audit')
report = dict(status='ROOT_SOURCE_ONLY_NEXT_ROUTE_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_whole_public_cuts_read=True, sources=28, cuts=cuts, cut_lines=lines,
    all_twelve_H15_outputs_retained=True, same_H15_fuel_result_and_full_after=True,
    same_finite_model_and_ranked=True, genuine_parent_admission_and_initial_Covered=True,
    same_global_initial_domains_Valid_Trace_Room=True,
    same_done_hit_readback_and_raw_miss_steps=True,
    physical_trace_requires_actual_prefix_admission=True,
    fabricated_contextual_receipt_or_second_execution=False,
    public_APIs_only=True, new_induction=False, new_global_helpers=0,
    native_Covered_only=True, proposed_source_target=[180, 215], proposed_source_hard_stop=230,
    budget_is_future_proposal_only=True,
    source_binding_clarification='Only the literal emptyDomain request has no binding obligations. The source can have other bindings.',
    independent_review_sha256=sha(audit / 'review.json'),
    fresh_baseline_and_exact_declaration_budget_gate_required=True,
    exact_header_proposal_authorized=False, body_proposal_authorized=False,
    compiler_authorized=False, prepared_tool_execution_authorized=False, whole_goal_complete=False)
save('root-next-inventory-review.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Next public API route reviewed\n\nRoot and independent reviews accept all28 source identities and34 public cuts.\nA future wrapper can keep the same H15 witness and all12 outputs.\nIt can use hit checked-state equality and actual miss prefix admission to derive native Covered.\nGenuine parent admission, initial Covered and the complete global packet remain.\nThe 180–215-line target and230-line stop are future proposals.\nA fresh baseline and exact declaration/local/budget gate must precede any body or compiler.\nThe whole goal stays ACTIVE.\n')
    output.write('Only this literal emptyDomain request has no binding obligations. The source can have other bindings.\n')
print(json.dumps(report))
