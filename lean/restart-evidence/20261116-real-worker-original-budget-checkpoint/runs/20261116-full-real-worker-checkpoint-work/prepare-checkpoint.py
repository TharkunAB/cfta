from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
base = root / 'lean/restart-evidence'
prior_work = base / '20261116-real-worker-task-induction-checkpoint-work'
packet = '20261116-real-worker-original-budget-checkpoint'
prior_packet = '20261116-real-task-flow-checkpoint'
code = 'e23fc6b1dde071c7a90cb5150b7386fa527c7821'
prior = '3329ad512b6af8c0f3da718224450e84d4cc7711'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip() == code
public = base / '20261116-full-real-worker-final-publication'
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] for c in result['checks'])
assert result['audited_theorems'] == 98096
assert result['individual_reports'] == 427
config = dict(result, checked_code=code, prior_checkpoint=prior, public_run=str(public),
    public_gates=5, explicit_reports=427, source_files=6130, direct_audit_imports=5130,
    board_prefix='current-board-full-', new_modules=1, new_public_theorems=2,
    old_non_audit_sources_byte_exact=6127, old_owner_and_audit_bytes_preserved_as_exact_blocks=True,
    original_full_real_target='549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607',
    original_c831_declaration='c831a364518a5fb5e9bce2008227efe44cd693e7c10442ad4eaa0c12f2b0ec8a',
    real_worker_task_and_depth_inductions_discharged=True,
    actual_shared_incoming_union_normal_proved=True, full_worker_union_normal_proved=False,
    every_emission_before_later_stop_covered=True, endpoint_resources_only_for_complete_returns=True,
    original_algorithm_budgets_unchanged=True, original_proof_limit=2000000,
    native_CM_query_scope='One literal initial node query; both complete memo families initially empty.',
    full_scope='One finite accepted completion of SAME original emitted partial root under ONE compatible assignment satisfying actual domains, paths, UF aliases, residuals, readback, parked recompletion and EVERY removed historical obligation on THAT branch. Keep original source/root/noStop, original fuels/budgets, ALL outcomes/emissions before later stop. Preserve typing/depth/completeness/preprocessing/LPO/order/multiplicity/lazy-demand/node-count/count/weight/training/both-rank-inverse/host-bounds/Haskell-correspondence contracts.')
(work / 'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
names = [work.name, prior_work.name, public.name, '20261116-full-real-worker-publication',
 '20261116-native-whole-real-worker-4m-and-actual-dispatch-check',
 '20261116-native-real-scan-statement-versus-proof-check',
 '20261116-native-shared-incoming-union-normal-check',
 '20261116-native-real-scan-scalar-opacity-check',
 '20261116-native-shared-incoming-union-normal-repaired-check',
 '20261116-native-whole-real-scalar-and-union-normal-check',
 '20261116-native-whole-real-scalar-root-and-union-normal-check',
 '20261116-native-whole-real-nested-root-and-union-normal-check',
 '20261116-current-real-worker-scan-statement-proof-diagnostics',
 '20261116-current-real-worker-scan-target-scalar-opacity-repair',
 '20261116-current-real-worker-scan-opaque-fold-sharing-draft',
 '20261116-current-real-worker-scan-scalar-root-projection-repair',
 '20261116-current-real-worker-scan-nested-root-simp-repair',
 '20261116-current-real-worker-depth-prepared-result-normalization-repair',
 '20261116-current-real-worker-original-scope-readonly-audit',
 '20261116-current-shared-incoming-union-normal-endpoint-draft',
 '20261116-current-shared-incoming-union-normal-skipped-gate-repair',
 '20261116-current-real-selected-prefix-union-normal-draft',
 '20261116-native-selected-prefix-union-normal-check',
 '20261116-current-past-entry-next-query-inner-laws-draft']
roots = [base / n for n in names]
assert all(p.is_dir() for p in roots)
(work / 'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots],indent=2)+'\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({
    'prior_immutable_checkpoints_retained':True,
    'selected_prefix_and_next_query_drafts_retained_unpromoted':True,
    'subsequent_live_checks_and_repairs_excluded':True},indent=2)+'\n')
(work / 'selection-review.json').write_text(json.dumps({
    'all_previous_proofs_counterexamples_repairs_and_drafts_preserved':True,
    'new_failed_attempts_and_diagnostics_preserved':True,
    'full_original_generic_resource_target_5493_proved':True,
    'compiled_objects_excluded':True,'original_full_objective_preserved':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text = (prior_work / name).read_text().replace(prior_packet,packet)
    text = text.replace("BASE = '10a69e8c44e5efdf6c982677442a71276ff3e60d'", "BASE = '"+prior+"'")
    text = text.replace('# Genuine real-task induction, captured startup and same-key cache payloads',
        '# Generic real-worker resource preservation at original budgets')
    (work / name).write_text(text)
text = (base / prior_packet / 'verify.py').read_text().replace(prior_packet,packet)
(work / 'verify.py').write_text(text)
print(json.dumps({'checked_code':code,'roots':len(roots),'public_gates':5}))
