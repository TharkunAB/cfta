from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = root / 'lean/restart-evidence/20261116-staged-child-incidence-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['sorryAx'] and not x['nonstandard_axioms'] and not x['diagnostics'] for x in report['checks'])
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
text = f'''Checked Source {code}. Specified staged-child incidence is proved. Actual tuple-trace inversion and genuine input-prefix induction retain the chosen child's entry caller/cache/queries, complete fragment prefix of the same length, root/callback indices, and actual tail trace to the SAME final endpoint/index. The direct selected bridge uses the literal SAME own preparation and staged[position] lookup. It retains assembled-fragment and residual-finish cache equalities. No association is inferred from output equality or a separate existential witness. The earlier exact captured invocation producer remains unchanged.

All-raw alias growth is now checked for actual local lookup, union, allocation and successful shared ChildDispatch.run. Lookup's forward finite-path law and successful union/link steps need NO Total/Safe/allocation-bound premise. Allocation leaves the forest unchanged. Literal successful shared child dispatch retains every entry SameClass pair at BOTH returned Core and attached cache Core, with their exact core equality and original five primitive fuels. Actual terminal-prefix mapM/forM, shared fold, incoming lookup/write and shallow paths supply the proof. No Packet, resource or future result is assumed. Owning GHC-style Notes state the scope and local proof reuse.

Next compose aliases through the actual enclosing eager/tuple/selected/captured/final recursive path and SAME emitted output. Whole-worker targetc4cb44f2 remains UNPROVED. Existing same-position raw-path congruence can now receive the authentic indexed child dispatch; its child-entry Roots invariant still needs an actual producer. The outer Nat proof must also attach EVERY removed event on THAT causal branch; explored siblings cannot supply this output's history. The largest gap remains ONE compatible rho for native domains, paths, UF, residual guards, readback and ALL removed/parked obligations, giving ONE finite accepted completion of the SAME original partial root. Existing E/R histories, immediate parked-suffix kept closure and conditional one-arrow same-snapshot model remain proved. Finite traces/local aliases do not establish joint completion. Full API, typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, host bounds, warm meanings and compiled Haskell correspondence remain in scope.

All FIVE gates pass: {report['source_files']} Source inventory files, {report['direct_audit_imports']} direct Audit imports, {report['individual_reports']} explicit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} resource/component reports, {report['audited_theorems']} audited declarations. Nine new reports cover nine public theorems in four modules. All prior 228 resource/component reports and all 6194 old non-Audit Source files remain exact. Old Audit bytes remain after four ordinary imports. Default new-module limits, original 2M owner limit, serial 8 GiB/zero swap, no sorryAx/nonstandard axioms. All primitive binder/path inference repairs and rejected preparation are preserved; failed checks receive no theorem credit. No Haskell/runtime change or reachable-source defect is claimed. EVERY future Haskell fix must be in FINDINGS.md. Goal ACTIVE; formalize publication remains explicitly authorized.'''
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Specified staged-child incidence and literal shared-child raw alias growth are checked', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'specified_staged_position_invocation_proved': True,
        'same_selected_preparation_child_incidence_proved': True,
        'literal_shared_child_all_raw_alias_growth_proved': True,
        'totality_safety_or_allocation_bound_added_to_child_alias_law': False,
        'whole_worker_raw_alias_transport_proved': False,
        'all_causal_removed_events_attached_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-staged-child-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
