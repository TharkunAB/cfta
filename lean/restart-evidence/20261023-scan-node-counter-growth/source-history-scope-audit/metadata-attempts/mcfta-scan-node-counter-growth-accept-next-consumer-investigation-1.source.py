exec(compile(open('/tmp/mcfta-scan-node-counter-growth-root-common.py').read(), '/tmp/mcfta-scan-node-counter-growth-root-common.py', 'exec'))
import re
owner = Path('/tmp/mcfta-after-scan-counter-investigation')
peer = Path('/tmp/mcfta-after-scan-counter-investigation-review')
checked_package(owner,'3499a8060ace413cc73093ddb9277b456e8a7ba8eb1a419b367055b600a7835f','10cd82aff7492f16e6500d61a4342b35577cb9a35e9e1cffbe5059fc375769d6')
checked_package(peer,'3adb39b8f3d7967dba7073be4cc22e0ae20c1342237a90e0145158b2b17a3534','612f63fd4ca90ccda26fa6a57bb51520ac3ba6659d9e4d3e3b8f090ffd1caed8')
assert sha(peer / 'review.json') == 'fb5775a0bc07e6b1def89f26829defa5b0e8b74217ab4a13089d0cbf0ce63045'
assert load(peer / 'review.json')['status'] == 'CLEAR'
index = load(owner / 'source-index.json')
assert len(index['sources']) == 10
cut_count = cut_lines = 0
for item in index['sources']:
    path = Path(item['path'])
    raw = path.read_bytes()
    assert raw == (owner / item['snapshot']).read_bytes()
    assert sha(path) == item['sha256'] and len(raw) == item['bytes']
    assert len(raw.splitlines()) == item['lines']
    assert re.findall(r'(?m)^(?:public )?import ([\w.]+)',raw.decode()) == item['imports']
    for cut in item['cuts']:
        expected = b''.join(raw.splitlines(keepends=True)[cut['start']-1:cut['end']])
        assert expected == (owner / cut['snapshot']).read_bytes()
        assert sha(owner / cut['snapshot']) == cut['sha256'] and len(expected) == cut['bytes']
        cut_count += 1
        cut_lines += cut['end']-cut['start']+1
assert (cut_count,cut_lines) == (17,442)
assert index['future_dependency']['status'] == 'PENDING_UNPROVED_H38'
assert not (ROOT / 'lean/MicroCFTA/SourceCurrentOriginalRowClusterScanNodeCounterGrowth.lean').exists()
archive(owner,'after-scan-counter-investigation')
archive(peer,'after-scan-counter-investigation-audit')
save('root-next-counter-consumer-investigation-review.json',dict(
    status='ACCEPTED_SOURCE_ONLY_NEXT_COUNTER_CONSUMER_ROUTE_PENDING_H38',
    root_whole_note_plain_contract_source_index_and_all_17_cuts_442_lines_read=True,
    ten_live_source_hashes_full_snapshots_and_import_lists_checked=True,
    root_all_ten_whole_source_manual_read_claimed=False,
    same_actual_Fin_Scan_done_chain_and_checked_work2_result_required=True,
    no_second_execution_helper_packet_predicate_counter_oracle_or_duplicated_semantics=True,
    Fin_induction_includes_empty_chain=True,existing_H36_execute_mono_supplies_final_bound=True,
    makeNode_next_is_upper_only=True,source_to_before_order_and_global_history_remain_separate=True,
    H38_dependency_pending_at_this_cut=True,current_H23_results_preserved=True,
    proposed_source_target=[55,90],proposed_hard_stop=120,
    exact_declaration_body_and_compiler_authorized=False,
    fresh_dependency_identity_and_exact_declaration_scope_required=True,
    independent_review_sha256=sha(peer / 'review.json'),goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the next observed-chain counter route as source-only planning conditional on H38.')
