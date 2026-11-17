from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
prior = 'db9c0d09b42d5680819f8b5aa6bfc6f310bbffbb'
public = base / '20261117-joint-held-ledger-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] and not item['diagnostics']
           and not item['sorryAx'] for item in report['checks'])
commit = json.loads((work / 'SOURCE-COMMIT.json').read_text())
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
assert code == commit['source_commit'] and commit['parent'] == prior
for name in commit['files']:
    assert subprocess.check_output(['git', 'show', code + ':' + name], cwd=root) == (root / name).read_bytes()
cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
assert usage['rate_limits']['primary']['used_percent'] <= 80
config = dict(report)
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-joint-held-',
    old_non_audit_non_owner_source_files_byte_exact=6234,
    old_owner_bytes_preserved_contiguously=2222363, old_owner_offset=0,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    old_audit_bytes_after_new_ordinary_imports=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    source_raw_target_compatibility_producer_proved=False,
    all_historical_same_output_semantic_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    source_pending_Profile_closure_proved=False, compiled_haskell_correspondence_proved=False,
    all_history9374_proved=True, full9374_candidate_frozen_uncompiled=False,
    output_equality_alone_does_not_identify_invocation=True, goal_active=True,
    prior_immutable_archive='20261117-all-outer-held-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
cut = datetime.datetime.fromisoformat(json.loads((work / 'START.json').read_text())['at']).timestamp() - 1
selected, skipped = [], []
for path in base.iterdir():
    if not path.is_dir() or not path.name.startswith('20261117-'):
        continue
    relative = str(path.relative_to(root))
    if ('checkpoint' in path.name or path.name == '20261117-all-outer-held-work'
            or path.stat().st_mtime < cut):
        skipped.append(relative)
    else:
        selected.append(relative)
assert len(selected) >= 8
assert str(work.relative_to(root)) in selected and str(public.relative_to(root)) in selected
for name in ['20261117-held-joint-event-ledger-core-draft',
             '20261117-actual-parked-joint-held-worker-event-matcher-repair',
             '20261117-joint-causal-held-captured-event-helper-draft']:
    assert str((base / name).relative_to(root)) in selected, name
(work / 'archive-roots.json').write_text(json.dumps(sorted(selected), indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(sorted(skipped), indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Preserve new source packets, first headers, all failed checks and repairs, marked open targets, and all publication controls. Preserve every prior immutable archive.',
    'prior_push_receipt_copied_to_new_work': True,
    'new_public_theorem_reports': report['new_public_theorems'],
    'new_private_component_reports': report['new_private_component_reports'],
    'new_relation_declaration_reports': report['new_relation_declaration_reports'],
    'new_declaration_checks': report['new_relation_declaration_checks'],
    'compiler_running_markers_are_not_liveness_evidence': True,
    'no_compiled_objects_or_import_overlays': True}, indent=2) + '\n')
fields = {'SOURCE_FILES': report['source_files'], 'AUDIT_IMPORTS': report['direct_audit_imports'],
    'AUDIT_REPORTS': report['individual_reports'], 'STANDARD_REPORTS': report['checks'][-1]['axiom_groups'],
    'FREE_REPORTS': report['checks'][-1]['axiom_free_reports'], 'INDEPENDENT_REPORTS': report['independent_reports'],
    'RESOURCE_REPORTS': report['resource_and_component_probes'], 'OWNER_REPORTS': report['owner_resource_probes'],
    'THEOREMS': report['audited_theorems'], 'NEW_PUBLIC_THEOREMS': report['new_public_theorems'],
    'NEW_PRIVATE_REPORTS': report['new_private_component_reports'],
    'NEW_DECLARATION_REPORTS': report['new_relation_declaration_reports'],
    'NEW_MODULES': report['new_modules'], 'CLEANUP': cleanup['cumulative_removed_bytes'],
    'USAGE': config['primary_usage_percent']}
note = (work / 'checkpoint-note.md').read_text()
for key, value in fields.items():
    note = note.replace('{{' + key + '}}', str(value))
assert set(__import__('re').findall(r'\{\{(.*?)\}\}', note)) == {'TIME', 'TREE', 'CODE'}
(work / 'checkpoint-note.md').write_text(note)
print(json.dumps({'checked_code': code, 'packet': '20261117-joint-held-ledger-checkpoint',
                  'roots': len(selected)}))
