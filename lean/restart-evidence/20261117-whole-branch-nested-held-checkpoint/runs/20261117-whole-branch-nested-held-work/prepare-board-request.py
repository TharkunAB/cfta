from pathlib import Path
from datetime import datetime
import json
import uuid

work = Path(__file__).parent
report = json.loads((work.parent / '20261117-whole-branch-nested-held-publication/checked.json').read_text())
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
at = datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
text = f'''[{at}] Checked Source {code}. The public actual_parked_same_joint_ledger_all_entries_held_history now derives ONE JointOutputLedgerAt for the SAME indexed actual output after a parked step, together with HeldFragmentHistory at EVERY visible operation INPUT in THAT list. EntriesHeld has no True case: parked, selected, prepare, opaque, finalize, recordTypes, and nested prepare/residual/dispatch are covered. Finalize uses before; recordTypes uses finished. The public worker derives its operational history internally from the original observed output and original admission. Genuine Nat-depth induction constructs ledger and held protection jointly. The captured case calls the checked original-budget producer ONCE and uses that SAME nested list and smaller-depth tail. All original source/root, supplied fuels, indices, duplicate occurrences and outputs before later stops remain. Primitive states hidden inside one atomic operation are outside this visible-input claim.

The original dfbf1278 terminal-Marker native-restriction contract also passes. At its original five independently supplied fuels and SAME actual returned store/readback, every member of the replacement language is the literal nullary Marker. Existing checked native intersection semantics supplies this restriction. The old conditional Satisfies clause remains. A restricted language can be empty: native inhabitance, Type/Marker class consistency, and ONE compatible finite model are not established.

The new frozen source-marker-class-compatibility-producer audit identifies the next real cut. The source U-arrow already has [Marker,U,U], but its Top own guard allocates no classes; its Marker target is inherited. The application own guard has three normalized classes, with Marker [1]=[2,0,0]. Existing TypePath and TypeSlot certify annotation phase/scope and permit Marker positions. ProgramSlots leaves these equality classes unmarked. We still need authentic source class-birth/path ownership through actual trie descent, UF terminal folds, native payload changes, stored equations and callbacks. Do not supply future roles/disjointness/inhabited intersections/model as assumptions. Generic checkEmpty=false can skip semantic emptiness; syntactic non-Empty is not inhabitance. Type fields can use their actual rigid source domains. No accepted-source collision or new Haskell defect is established.

All FIVE publication gates pass: {report['source_files']} Source files, {report['direct_audit_imports']} Audit imports, {report['individual_reports']} Audit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} component reports and {report['audited_theorems']} audited declarations. Three new public theorems, fourteen private components, two modules. All old2320102 owner bytes remain contiguous at offset67; all6237 other old non-Audit Source files stay exact. Original proof limits and runtime budgets remain; new owner limits200000/default. Every failed first packet and repair remains. A lost wrapper143 did not terminate its systemd .scope; the raw compiler completed250 reports and has an explicit separate recovery receipt. Later normal publication passed all5gates independently. Keep stdout in a regular file and inspect the actual .scope before any restart. No sorryAx or nonstandard axiom in passed checks.

Full goal remains ONE finite accepted completion of the SAME original emitted root satisfying actual native domains, paths, UF, residuals, readback, parked recompletion and EVERY causal historical obligation under ONE assignment. Preserve all typing/depth/completeness/preprocessing/LPO/order/multiplicity/lazy-demand/exact-size/count/weights/training/rank/host/Haskell contracts. No Haskell source changed; EVERY future Haskell fix belongs in root FINDINGS.md for the external agent. Goal ACTIVE; origin/formalize pushes authorized.'''
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Every visible input on one actual branch retains held history', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'new_public_theorem_reports': 3, 'new_private_component_reports': 14, 'new_modules': 2,
        'all_visible_operation_entries_held_proved': True,
        'source_terminal_marker_native_restriction_proved': True,
        'source_type_marker_class_consistency_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-whole-branch-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
