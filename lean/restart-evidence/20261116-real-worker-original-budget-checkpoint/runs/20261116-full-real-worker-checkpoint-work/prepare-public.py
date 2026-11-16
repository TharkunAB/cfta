from pathlib import Path
import subprocess

work = Path(__file__).parent
prior_work = work.parent / '20261116-real-worker-task-induction-checkpoint-work'
text = (prior_work / 'prepare-subset-public.py').read_text()
replacements = {
 '20261116-native-real-task-and-opaque-subset-check': '20261116-native-whole-real-nested-root-and-union-normal-check',
 '20261116-real-worker-task-flow-publication': '20261116-full-real-worker-publication',
 '20261116-real-worker-assembly-checkpoint': '20261116-real-task-flow-checkpoint',
 '20261116-real-worker-assembly-publication': '20261116-real-worker-task-flow-publication',
 '10a69e8c44e5efdf6c982677442a71276ff3e60d': '3329ad512b6af8c0f3da718224450e84d4cc7711',
 "work/'Task123Probes.lean.txt'": "work/'ResourceProbes.lean.txt'",
 '6126': '6127', '6129': '6130', '5129': '5130',
 '123': '136', '425': '427',
 "'whole_real_worker_at_any_budget_proved':False": "'whole_real_worker_at_any_budget_proved':True",
 "'new_public_theorems':1": "'new_public_theorems':2",
 "'unpromoted_original_real_target_5493_frozen':True": "'original_real_header_5493_exact':True",
 "'SourceCurrentAllocatedNativePastEntryInnerPayloadTransport']":
     "'SourceCurrentAllocatedNativePastEntryInnerPayloadTransport', 'SourcePruningEnumerationSharedIncomingUnionNormal']",
 "laws=['MicroCFTA.SourceCurrentAllocatedNativePastEntryInnerPayloadTransport.inner_payloads_of_past_authentic_entry_at_equal_key']":
     "laws=['MicroCFTA.SourcePruningEnumerationSharedEagerReservation.runEager_real_emitted_complete_resources_at_any_budget', 'MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal.run_unionNormal']",
 "text='import MicroCFTA.SourceCurrentAllocatedNativePastEntryInnerPayloadTransport\\n'":
     "text='import MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal\\n'",
 "==20": "==22", ",20)": ",22)", "'independent_reports':20": "'independent_reports':22",
}
for old, new in replacements.items():
    assert old in text, old
    text = text.replace(old, new)
marker = "(runtime/'check.py').write_text(driver)"
assert marker in text
text = text.replace(marker, "driver=driver.replace(\"+\"+repr(\"\\\\n\"), \"+\"+repr(\"\\n\"))\n" + marker)
helper = work / 'prepare-public-core.py'
helper.write_text(text)
subprocess.run(['python3', str(helper)], check=True)
