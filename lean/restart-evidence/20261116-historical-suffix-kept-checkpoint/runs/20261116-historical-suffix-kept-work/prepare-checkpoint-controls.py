from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old = base / '20261116-expanded-birth-history-work'
prior = 'afff98c80ededd9f3b3003a9dcd6b1fb230c2902'
packet_name = '20261116-historical-suffix-kept-checkpoint'
public = base / '20261116-immediate-historical-suffix-kept-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] and not x['diagnostics'] and not x['sorryAx'] for x in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
assert code == json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert code != prior
for name in ['SourcePruningEnumerationSharedEagerReservation.lean', 'Audit.lean']:
    relative = 'lean/MicroCFTA/' + name
    assert subprocess.check_output(['git', 'show', code + ':' + relative], cwd=root) == (root / relative).read_bytes()
cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
config = dict(report)
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-historical-suffix-',
    old_non_owner_non_audit_sources_byte_exact=6183, prior_owner_bytes_after_one_ordinary_import=True,
    old_audit_bytes_retained_as_exact_prefix=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'], primary_usage_checked_at=usage['timestamp'],
    whole_worker_expanded_birth_history_proved=True, whole_worker_entry_bucket_kept_producer_proved=True,
    original_906_statement_and_every_old_proof_preserved=True,
    same_snapshot_one_arrow_bucket_conditional_recompletion_proved=True,
    source_raw_target_compatibility_producer_proved=False, all_historical_same_output_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False, source_pending_Profile_closure_proved=False,
    compiled_haskell_correspondence_proved=False, next_causal_origin_candidate_uncompiled=True, goal_active=True,
    prior_immutable_archive='20261116-expanded-birth-and-dependency-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
names = [work.name, public.name, '20261116-real-parked-immediate-suffix-kept-check',
         '20261116-real-parked-immediate-suffix-kept-draft',
         '20261116-immediate-suffix-kept-owner-boundary-audit',
         '20261116-removed-arrow-target-compatibility-producer-audit',
         '20261116-real-eager-captured-output-causal-origin-draft']
assert all((base / name).is_dir() for name in names)
(work / 'archive-roots.json').write_text(json.dumps(['lean/restart-evidence/' + name for name in names], indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({'prior_immutable_archive': config['prior_immutable_archive'], 'policy': 'Preserve all earlier immutable archives. Only this explicit new batch is copied.'}, indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({'prior_checkpoint': prior, 'selected_roots': len(names),
    'policy': 'Lossless new proof inputs, exact public transformation, strict checks, causal audits and marked uncompiled next target; no copied compiler objects.',
    'prior_push_receipt_copied_to_new_work': True, 'frozen_next_candidate_is_not_proof_credit': True,
    'compiler_running_markers_are_not_liveness_evidence': True}, indent=2) + '\n')
fields = {'SOURCE_FILES': report['source_files'], 'AUDIT_IMPORTS': report['direct_audit_imports'],
          'AUDIT_REPORTS': report['individual_reports'], 'STANDARD_REPORTS': report['checks'][-1]['axiom_groups'],
          'FREE_REPORTS': report['checks'][-1]['axiom_free_reports'], 'INDEPENDENT_REPORTS': report['independent_reports'],
          'RESOURCE_REPORTS': report['owner_resource_probes'], 'RESOURCE_STANDARD': report['checks'][1]['axiom_groups'],
          'RESOURCE_FREE': report['checks'][1]['axiom_free_reports'], 'THEOREMS': report['audited_theorems'],
          'OLD_SOURCES': 6183, 'CLEANUP': cleanup['cumulative_removed_bytes'], 'USAGE': config['primary_usage_percent']}
note = (work / 'checkpoint-note.md').read_text()
for key, value in fields.items():
    note = note.replace('{{' + key + '}}', str(value))
(work / 'checkpoint-note.md').write_text(note)
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    text = (old / name).read_text().replace('20261116-expanded-birth-and-dependency-checkpoint', packet_name)
    text = text.replace('201a254faee6436e9172581d526f5b1e0ce44889', prior)
    text = text.replace('# Whole-worker birth history and actual dependency closure', '# Removed-bucket closure through the actual parked restart')
    (work / name).write_text(text)
print(json.dumps({'checked_code': code, 'packet': packet_name, 'roots': len(names)}))
