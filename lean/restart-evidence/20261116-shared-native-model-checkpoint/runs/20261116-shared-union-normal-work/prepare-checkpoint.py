from pathlib import Path
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta');base=root/'lean/restart-evidence';work=Path(__file__).parent
prior_work=base/'20261116-native-origin-invariants-work'
packet='20261116-shared-native-model-checkpoint'
prior_packet='20261116-native-origin-invariants-checkpoint'
code='8b279e6e7355acf0210debad6a0a2e9dab8097c7'
prior='0feb93907f8b8f0f49deb4458fe86c6430e261ee'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==code
public=base/'20261116-shared-native-model-publication'
result=json.loads((public/'checked.json').read_text())
assert len(result['checks'])==5 and all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
assert result['audited_theorems']==98180 and result['individual_reports']==442
old_config=json.loads((base/prior_packet/'checkpoint.json').read_text())
config=dict(result,checked_code=code,prior_checkpoint=prior,public_run=str(public),
 public_gates=5,explicit_reports=442,source_files=6138,direct_audit_imports=5138,
 board_prefix='current-board-model-',new_modules=6,new_public_theorems=13,
 old_non_audit_sources_byte_exact=6131,old_owner_and_audit_bytes_preserved_as_exact_blocks=True,
 real_worker_task_and_depth_inductions_discharged=True,
 every_emission_before_later_stop_covered=True,endpoint_resources_only_for_complete_returns=True,
 original_full_real_target='549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607',
 pending_assignment_scope='One current assignment, Safe/Stratified and empty pending buckets with a common admitted fallback; existing evaluator reused. No historical obligation, residual guard or original-root acceptance claim.',
 past_gamma_scope='One actual old cold-produced node cell under a later actual equal-key entry with same tables/full P/original heights; arbitrary old warm producer ownership remains open.',
 full_scope=old_config['full_scope'])
(work/'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
names=[work.name,public.name,
 '20261116-current-real-selected-preparation-union-normal-union-readback-repair',
 '20261116-native-selected-preparation-union-normal-repaired-check',
 '20261116-current-shared-dispatch-union-normal-draft',
 '20261116-native-shared-dispatch-union-normal-check',
 '20261116-current-shared-dispatch-union-normal-id-pure-repair',
 '20261116-native-shared-dispatch-union-normal-repaired-check',
 '20261116-current-shared-dispatch-union-normal-explicit-outcome-repair',
 '20261116-native-shared-dispatch-union-normal-explicit-check',
 '20261116-current-shared-cached-terminal-union-normal-draft',
 '20261116-current-shared-child-union-normal-draft',
 '20261116-current-past-gamma-equal-entry-payload-draft',
 '20261116-current-past-gamma-equal-entry-payload-minimal-draft',
 '20261116-current-past-gamma-equal-entry-payload-projection-repair',
 '20261116-current-stratified-pending-assignment-draft',
 '20261116-current-stratified-pending-domain-existing-engine-repair',
 '20261116-current-none-pending-bucket-origin-audit',
 '20261116-terminal-gamma-pending-candidates-check',
 '20261116-gamma-child-candidates-check',
 '20261116-pending-domain-existing-engine-check']
roots=[base/name for name in names];assert all(p.is_dir() for p in roots)
(work/'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots],indent=2)+'\n')
(work/'skipped-published-roots.json').write_text(json.dumps({
 'prior_immutable_checkpoints_retained':True,'active_worker_U_and_None_inductions_not_falsely_sealed':True,
 'active_source_domain_ownership_work_remains_local':True},indent=2)+'\n')
(work/'selection-review.json').write_text(json.dumps({
 'all_previous_proofs_counterexamples_repairs_and_drafts_preserved':True,
 'failed_warm_projection_and_duplicate_evaluator_draft_preserved':True,
 'existing_evaluator_and_original_worker_byte_exact':True,'compiled_objects_excluded':True,
 'full_objective_preserved':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text=(prior_work/name).read_text().replace(prior_packet,packet)
    text=text.replace("BASE = '1f61f22734b91de31c05281a205f933cb4773ba8'","BASE = '"+prior+"'")
    text=text.replace('# Actual prefix normality and next-query inherited laws',
      '# Native continuation invariants and one current assignment')
    (work/name).write_text(text)
(work/'verify.py').write_text((base/prior_packet/'verify.py').read_text().replace(prior_packet,packet))
print(json.dumps({'checked_code':code,'roots':len(roots),'public_gates':5}))
