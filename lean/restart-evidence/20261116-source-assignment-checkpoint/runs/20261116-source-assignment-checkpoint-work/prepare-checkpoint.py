from pathlib import Path
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old_work = base / '20261116-worker-invariants-work'
old_packet = '20261116-worker-invariants-checkpoint'
packet = '20261116-source-assignment-checkpoint'
code = '3393b0245ca606d4d217677cc2cbd79883443b8b'
prior = 'be7969ef9fea1e01cf3c8aeaf58e30b3ec92c70f'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
public = base / '20261116-source-assignment-events-publication'
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] for c in result['checks'])
assert result['audited_theorems'] == 98482 and result['individual_reports'] == 484
old = json.loads((base / old_packet / 'checkpoint.json').read_text())
config = dict(result, checked_code=code, prior_checkpoint=prior, public_run=str(public),
              public_gates=5, explicit_reports=484, source_files=6156, direct_audit_imports=5156,
              board_prefix='current-board-assignment-', new_modules=2, new_public_theorems=4,
              old_non_audit_sources_byte_exact=6151, old_owner_exact_prefixes=2,
              every_old_header_and_proof_preserved=True,
              actual_child_none_buckets_private_passed=True, child_source_promoted=False,
              full_scope=old['full_scope'])
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
phase = base / '20261116-source-assignment-events-work'
names = {phase.name, work.name, public.name}
for p in phase.glob('*.py'):
    names.update(n for n in re.findall(r'20261116-[a-z0-9-]+', p.read_text()) if (base / n).is_dir())
names -= {old_packet, '20261116-worker-origin-work', '20261116-worker-invariants-publication',
          '20261116-shared-native-model-publication', '20261116-worker-success-and-operands-check',
          '20261116-current-source-real-done-assignment-facts-scope-repair',
          '20261116-current-stored-dispatch-enter-identities-draft'}
names.update(['20261116-source-assignment-event-aliases-check',
              '20261116-current-real-child-none-buckets-draft',
              '20261116-current-real-child-none-typing-repair',
              '20261116-current-real-child-none-source-match-repair',
              '20261116-child-none-source-match-check',
              '20261116-current-real-worker-none-buckets-whole-draft',
              '20261116-current-source-chronological-cm-contract-audit',
              '20261116-current-source-issued-domain-enter-origin-draft',
              '20261116-current-real-eager-parked-raw-bucket-receipt-draft',
              '20261116-current-real-eager-parked-raw-bucket-observer-boundary-repair'])
roots = [base / n for n in sorted(names)]
assert all(p.is_dir() for p in roots)
(work / 'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots], indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({
    'earlier_immutable_checkpoints_preserved': True,
    'all_new_frozen_next_candidates_archived_with_no_false_credit': True,
}, indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'all_old_proofs_counterexamples_repairs_and_drafts_preserved': True,
    'failed_preparation_and_strict_runs_preserved': True,
    'malformed_first_parked_observer_preserved_and_excluded': True,
    'old_owner_bytes_are_exact_prefixes': True,
    'source_factory_retained_guard_and_history_boundary_explicit': True,
    'compiled_objects_excluded': True, 'full_objective_preserved': True,
}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py']:
    text = (old_work / name).read_text().replace(old_packet, packet)
    text = text.replace("BASE = '1886de428b8c151e1ff335d09ffe41459239a448'", "BASE = '" + prior + "'")
    text = text.replace('# Actual eager-worker normality and current-state models',
                        '# Actual source assignments and canonical entry receipts')
    (work / name).write_text(text)
(work / 'verify.py').write_text((base / old_packet / 'verify.py').read_text().replace(old_packet, packet))
print(json.dumps({'checked_code': code, 'roots': len(roots), 'public_gates': 5}))
