from pathlib import Path
import subprocess

work=Path(__file__).parent
prior=work.parent/'20261116-full-real-worker-checkpoint-work'
text=(prior/'prepare-final-public.py').read_text()
replacements={
 '20261116-native-whole-real-nested-root-and-union-normal-check':'20261116-native-prefix-union-and-next-query-repaired-check',
 '20261116-full-real-worker-final-publication':'20261116-native-origin-invariants-publication',
 '20261116-real-task-flow-checkpoint':'20261116-real-worker-original-budget-checkpoint',
 '20261116-real-worker-task-flow-publication':'20261116-full-real-worker-final-publication',
 '3329ad512b6af8c0f3da718224450e84d4cc7711':'1f61f22734b91de31c05281a205f933cb4773ba8',
 "changed={'lean/MicroCFTA/Audit.lean','lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'}":
     "changed={'lean/MicroCFTA/Audit.lean'}",
 '6127':'6129','6130':'6132','5130':'5132','427':'429',
 "'SourcePruningEnumerationSharedIncomingUnionNormal']":
     "'SourcePruningEnumerationSharedIncomingUnionNormal','SourcePruningEnumerationSelectedPrefixUnionNormal','SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws']",
 "laws=['MicroCFTA.SourcePruningEnumerationSharedEagerReservation.runEager_real_emitted_complete_resources_at_any_budget', 'MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal.run_unionNormal']":
     "laws=['MicroCFTA.SourcePruningEnumerationSelectedPrefixUnionNormal.runPrefix_unionNormal','MicroCFTA.SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws.next_node_query_preserves_actual_past_inner_payloads']",
 "text='import MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal\\n'":
     "text='import MicroCFTA.SourcePruningEnumerationSelectedPrefixUnionNormal\\nimport MicroCFTA.SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws\\n'",
 '==22':'==24',',22)':',24)',"'independent_reports':22":"'independent_reports':24",
 "'whole_warm_source_history_proved':False":
     "'whole_warm_source_history_proved':False,'next_actual_query_inner_laws_from_past_producers_proved':True,'actual_selected_prefix_union_normal_proved':True,'full_worker_union_normal_proved':False",
}
for old,new in replacements.items():
    assert old in text,old
    text=text.replace(old,new)
for name,data in [('BASE-OWNER.lean.txt',(work.parents[1]/'MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes()),
                  ('ResourceProbes.lean.txt',(prior/'ResourceProbes.lean.txt').read_bytes())]:
    p=work/name;assert not p.exists();p.write_bytes(data)
helper=work/'prepare-public-core.py';helper.write_text(text)
subprocess.run(['python3',str(helper)],check=True)
