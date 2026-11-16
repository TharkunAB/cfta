from pathlib import Path
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
prior_work=base/'20261116-full-real-worker-checkpoint-work'
packet='20261116-native-origin-invariants-checkpoint'
prior_packet='20261116-real-worker-original-budget-checkpoint'
code='dfa9555cb178d1822889f46797e84cf79197d1ba'
prior='1f61f22734b91de31c05281a205f933cb4773ba8'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==code
public=base/'20261116-native-origin-invariants-publication'
result=json.loads((public/'checked.json').read_text())
assert len(result['checks'])==5
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
assert result['audited_theorems']==98135 and result['individual_reports']==429
config=dict(result,checked_code=code,prior_checkpoint=prior,public_run=str(public),
    public_gates=5,explicit_reports=429,source_files=6132,direct_audit_imports=5132,
    board_prefix='current-board-origin-',new_modules=2,new_public_theorems=2,
    old_non_audit_sources_byte_exact=6129,old_owner_and_audit_bytes_preserved_as_exact_blocks=True,
    real_worker_task_and_depth_inductions_discharged=True,
    actual_shared_incoming_union_normal_proved=True,
    every_emission_before_later_stop_covered=True,endpoint_resources_only_for_complete_returns=True,
    original_full_real_target='549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607',
    native_CM_query_scope='One literal initial node query; both complete memo families initially empty.',
    next_query_scope='Same actual old-source entry and full inherited tables; one literal next node execute, original newFuel and actual InputsThrough/FieldsThrough, full P, all four auxiliary Returned laws and two node raw laws. Does not supply later cross-source C/M past Gamma.',
    full_scope='ONE finite accepted completion of SAME original emitted partial root under ONE compatible assignment satisfying actual domains, paths, UF aliases, residuals, readback, parked recompletion and EVERY removed historical obligation on THAT branch. Keep original source/root/noStop, original fuels/budgets and ALL outcomes/emissions before later stops. Preserve separate typing/depth/completeness/preprocessing/LPO/order/multiplicity/lazy-demand/node-count/count/weight/training/both-rank-inverse/host-bounds/Haskell contracts.')
(work/'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
names=[work.name,public.name,
 '20261116-native-prefix-union-and-next-query-inner-laws-check',
 '20261116-native-prefix-union-and-next-query-repaired-check',
 '20261116-current-real-selected-prefix-union-normal-state-and-membership-repair',
 '20261116-current-real-selected-prefix-union-normal-ite-names-repair',
 '20261116-current-past-entry-next-query-domain-open-repair',
 '20261116-current-next-query-four-law-induction-scope-audit',
 '20261116-current-real-selected-preparation-union-normal-draft',
 '20261116-native-selected-preparation-union-normal-check']
roots=[base/n for n in names];assert all(p.is_dir() for p in roots)
(work/'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots],indent=2)+'\n')
(work/'skipped-published-roots.json').write_text(json.dumps({'prior_immutable_checkpoints_retained':True,
    'subsequent_live_preparation_repairs_and_further_warm_work_excluded':True,
    'selected_preparation_first_draft_and_failed_check_retained':True},indent=2)+'\n')
(work/'selection-review.json').write_text(json.dumps({'all_previous_proofs_counterexamples_repairs_and_drafts_preserved':True,
    'new_failed_attempts_and_surgical_repairs_retained':True,'full_P_and_original_fuels_retained':True,
    'compiled_objects_excluded':True,'full_objective_preserved':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text=(prior_work/name).read_text().replace(prior_packet,packet)
    text=text.replace("BASE = '3329ad512b6af8c0f3da718224450e84d4cc7711'", "BASE = '"+prior+"'")
    text=text.replace('# Generic real-worker resource preservation at original budgets',
        '# Actual prefix normality and next-query inherited laws')
    (work/name).write_text(text)
text=(base/prior_packet/'verify.py').read_text().replace(prior_packet,packet)
(work/'verify.py').write_text(text)
print(json.dumps({'checked_code':code,'roots':len(roots),'public_gates':5}))
