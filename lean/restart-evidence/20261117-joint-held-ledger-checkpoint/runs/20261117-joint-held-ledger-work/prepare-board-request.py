from pathlib import Path
import json
import uuid

work = Path(__file__).parent
report = json.loads((work.parent / '20261117-joint-held-ledger-publication/checked.json').read_text())
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert len(report['checks']) == 5 and report['joint_held_event_history_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           for c in report['checks'])
text = f"""Checked Source {code}. Original a3c927d3 worker statement is proved. After an authentic parked clear, it derives ONE indexed JointOutputLedgerAt and HeldFragmentHistory for the visible before-cache of every recorded parked, selected and prepare operation in THAT SAME event list. It retains original bucket/handle/lookup/boundary witnesses, original supplied fuels/depth/index and outputs before later stops. Nested events remain in the same list with their authentic invocation, receipt, consumer index, finalizer and false callback.

The mutual core recurses on ONE Held derivation. It uses that constructor's literal fields to derive Canonical/Total and constructs the joint ledger and event-membership protection together. It never separately eliminates a Qualified proof to obtain hidden fields. Captured nested events come from ONE actual callback invocation. The core's two public adapters explicitly consume a Held qualification. The worker theorem internally obtains that qualification from9374 and derives the SAME immediate continuation's Canonical/Total from original Canonical, Packet.safe, actual prefix facts and callback-frame equality. No future history, Packet, R, model or callback supplier is added. Initial Canonical is a genuine past requirement; Packet alone supplies Total. Original9374 remains unchanged and still has no Canonical premise.

The exact property is OuterEntriesHeld: parked/selected/prepare entry caches only. Opaque/finalize/recordTypes/nested cases are True. It does not establish R at all nested or primitive cuts, native membership, TypeIn, guard truth or one finite assignment. Prop proof indices still do not identify hidden constructor data. The core shared predicate and headers remain exact. The worker theorem declaration is byte-exact to firsta3c; only the obsolete OPEN status comment was removed in normal Source. One failed worker check found a final matcher conversion; cases on the SAME event fixed it without new witnesses or assumptions.

Next audit404fcaaf identifies an event-indexed companion of the actual literal tuple/child/row Task.work Current induction. Actual captured code already derives its required PAST Ledger/Origin/Current and held scope. OPEN headerc316720e returns one ChildrenLedger and R at visible prepare/residual/dispatch INPUT caches while retaining returned Current. It is UNPROVED, adds no framework and does not permit arbitrary callbacks, endpoint backtransport or no-allocation prefix equality. The invalid-scope old20b target remains OPEN.

Largest gap remains ONE finite accepted completion of the SAME original emitted root under ONE compatible assignment satisfying current native domains, paths, UF, residuals, readback and EVERY historical obligation on that branch. Preserve authentic Type/Marker roles, class consistency and role-safe stored equations; derive actual order/compatibility and one typed evaluator; preserve native domains/guards through ordered recompletion. Do not splice separate assignments or sibling histories. Full typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, warm C/M/Returned/mixed/Profile, host bounds and compiled Haskell correspondence remain open.

All FIVE gates pass: {report['source_files']} Source files, {report['direct_audit_imports']} Audit imports, {report['individual_reports']} explicit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} resource/component reports and {report['audited_theorems']} audited declarations. Three new public theorems, nine private components, two normal modules and one definition check; the standalone helper check is not counted twice. ALL6235 old non-Audit sources and the ENTIRE2222363-byte owner remain exact. All226 owner and136 original probes remain. Default new proof limits, original old limits, serial8GiB/zero swap; no sorryAx/nonstandard axiom/suppression/runtime change. No Haskell source changed. EVERY future Haskell fix must be recorded in FINDINGS.md. Goal ACTIVE; formalize push authorized."""
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'One causal ledger now carries canonical facts and outer entry protection', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'new_public_theorem_reports': 3, 'new_private_component_reports': 9, 'new_modules': 2,
        'joint_held_event_history_proved': True, 'worker_a3c_theorem_declaration_byte_exact': True,
        'core_shared_predicate_and_headers_byte_exact': True, 'entire_previous_resource_owner_byte_exact': True,
        'nested_cut_protection_proved': False, 'actual_source_type_marker_role_preservation_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-joint-held-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
