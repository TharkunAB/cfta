from pathlib import Path
from datetime import datetime
import json
import uuid

work = Path(__file__).parent
report = json.loads((work.parent / '20261117-nested-held-entry-publication/checked.json').read_text())
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert len(report['checks']) == 5
assert report['actual_captured_invocation_nested_input_protection_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
at = datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
text = f'''[{at}] Checked Source {code}. The original c316720e completed-invocation theorem and original fca9b5f7 public captured-invocation theorem are proved. Original Packet/resources, selection/reservation, genuine PAST anchor history, literal successful preparation, completed native scan prefix and SAME CapturedCallbackInvocationAt produce ONE public CapturedEventLedgerAt and held protection at every recorded prepare/residual/dispatch INPUT cache of THAT SAME event list. Private Ledger/Origin/Current/HeldScope are derived internally. Actual finalizer and false recordTypes observations stay joint. No future Current, model, callback or history supplier is added. Original supplied fuels, indices, duplicate occurrences and outputs before later stops remain.

Genuine tuple/child/row Task.work induction constructs the SAME nested ledger and returned Current together. A checked input factor uses only stored past scope and tuple receipts. The guarded transport retains the SAME eager head/tail events under actual lower inputs, including stopped exits. The public proof calls c316 ONCE, builds SelectedLedgerAt.singleton_done from those child events and proves authenticity on THAT selected ledger. It never chooses a second generic event witness. There is no endpoint backtransport or unchanged earlier native-heap premise.

Boundary: this is one completed captured invocation. A single whole-output joint ledger with this protection at EVERY capture is still OPEN; the prior OuterEntriesHeld nested case remains True. Atomic primitive interiors and ONE finite accepted completion of the SAME original emitted root are also OPEN. The latter must satisfy actual native domains, paths, UF, residuals, readback and EVERY causal historical obligation under ONE assignment. Preserve the original source/root/noStop and every supplied budget; do not splice sibling histories or assignments.

The semantic audit identifies the missing source-qualified Type/Marker demand-to-class producer through actual merges, stored equations and callback tails. ProgramSlots does not certify those classes. Existing Step.verified already supplies native-query intersection meaning at the same actual completed endpoint under its genuine admission/memo premises. This is positive reuse, not a new global meaning theorem. The optional Marker-native restriction header remains OPEN and is only a local packaging target; an empty subset is not a model witness. Type fields can use their actual rigid source domain, so an all-U membership condition would be too strong.

All FIVE publication gates pass: {report['source_files']} Source files, {report['direct_audit_imports']} Audit imports, {report['individual_reports']} Audit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} resource/component probes and {report['audited_theorems']} audited declarations. Two new public theorems, ten private components, one new module and five private definition checks. All235 owner probes and136 original probes remain. The whole old2222363-byte owner stays exact after196 bytes of ordinary imports; all6236 other old non-Audit Source files remain exact. First phase/c316/fca declarations stay exact; three unused forall binders have documented alpha renames. Every failed attempt and repair is retained. New limits200000/default, all old limits unchanged, serial8GiB/zero swap. No sorryAx, nonstandard axiom, suppression or runtime change. No Haskell source changed; EVERY future Haskell fix belongs in FINDINGS.md. All broader API/typing/depth/completeness/preprocessing/LPO/order/multiplicity/lazy-demand/size/count/weights/training/rank/host/Haskell contracts remain in scope. Goal ACTIVE; formalize pushes authorized.'''
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Actual captured invocations retain one protected nested event ledger', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'new_public_theorem_reports': 2, 'new_private_component_reports': 10, 'new_modules': 1,
        'closed_c316_original_budget_proved': True,
        'actual_captured_invocation_nested_input_protection_proved': True,
        'whole_worker_joint_nested_protection_proved': False,
        'actual_source_type_marker_role_preservation_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-nested-held-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
