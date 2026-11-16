from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
prior_work = base / '20261116-shared-union-normal-work'
prior_packet = '20261116-shared-native-model-checkpoint'
packet = '20261116-worker-invariants-checkpoint'
code = '6717634e5885f45ffd0d09413bd062feb959f90b'
prior = '1886de428b8c151e1ff335d09ffe41459239a448'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
public = base / '20261116-worker-invariants-publication'
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] for c in result['checks'])
assert result['audited_theorems'] == 98478 and result['individual_reports'] == 480
old_config = json.loads((base / prior_packet / 'checkpoint.json').read_text())
config = dict(result, checked_code=code, prior_checkpoint=prior, public_run=str(public),
              public_gates=5, explicit_reports=480, source_files=6154, direct_audit_imports=5154,
              board_prefix='current-board-invariants-', new_modules=16, new_public_theorems=38,
              old_non_audit_sources_byte_exact=6137,
              old_owner_and_audit_bytes_preserved_as_exact_blocks=True,
              real_worker_task_and_depth_inductions_discharged=True,
              every_emission_before_later_stop_covered=True,
              endpoint_resources_only_for_complete_returns=True,
              original_full_real_target='549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607',
              original_full_union_normal_target='dfcf91be896f56ea6eee3993bb4cd1a30c2fb43113873e1981670ed54991027f',
              stopped_endpoint_union_normal_proved=True,
              actual_source_enter_full_operands_proved=True,
              full_scope=old_config['full_scope'])
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
names = set(json.loads((work / 'archive-roots-review.json').read_text()))
names.update(p.name for p in base.glob('20261116-current-record-types-values-*') if p.is_dir())
names.update([work.name, '20261116-current-source-real-done-assignment-draft',
              '20261116-current-source-real-done-assignment-facts-scope-repair',
              '20261116-current-stored-dispatch-enter-identities-draft',
              '20261116-current-source-canonical-old-entry-receipt-draft'])
roots = [base / name for name in sorted(names)]
assert all(p.is_dir() for p in roots)
(work / 'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots], indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({
    'prior_immutable_checkpoints_retained': True,
    'active_full_None_and_child_None_proof_directories_not_falsely_sealed': True,
    'all_frozen_next_factory_and_actual_entry_candidates_archived_uncompiled': True,
}, indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'all_previous_proofs_counterexamples_repairs_and_drafts_preserved': True,
    'failed_strict_runs_and_exact_repairs_preserved': True,
    'original_worker_owner_and_all_old_non_audit_sources_byte_exact': True,
    'frozen_next_candidates_explicitly_uncompiled': True,
    'compiled_objects_excluded': True,
    'full_objective_preserved': True,
}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py']:
    text = (prior_work / name).read_text().replace(prior_packet, packet)
    text = text.replace("BASE = '0feb93907f8b8f0f49deb4458fe86c6430e261ee'", "BASE = '" + prior + "'")
    text = text.replace('# Native continuation invariants and one current assignment',
                        '# Actual eager-worker normality and current-state models')
    (work / name).write_text(text)
(work / 'verify.py').write_text((base / prior_packet / 'verify.py').read_text().replace(prior_packet, packet))
print(json.dumps({'checked_code': code, 'roots': len(roots), 'public_gates': 5}))
