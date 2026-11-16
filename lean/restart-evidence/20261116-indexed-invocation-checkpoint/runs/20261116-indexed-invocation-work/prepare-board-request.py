from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = root / 'lean/restart-evidence/20261116-indexed-causal-invocation-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['sorryAx'] and not x['nonstandard_axioms'] and not x['diagnostics'] for x in report['checks'])
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
text = f'''Checked Source {code}. The local captured-row invocation gap is closed. Three concrete mutually inductive Prop relations retain literal child dispatch, ordered tuple callbacks and selected preparation. Their producers return the executed invocation derivation and full output block at the SAME terminal index. The actual eager producer uses genuine smaller-height recursion and actual shallow fallback. The stronger real_eager_captured_output_causal_callback_restart_origin (header3337c1ab) retains ALL original2a parameters, output premise, witnesses and conclusions, and produces CapturedCallbackInvocationAt for THOSE SAME fields. It obtains the trace and block jointly, then uses that receipt's literal Finalize and false recordTypes observations. It does not splice the older extensional theorem's witnesses. Original fuels, budgets, duplicate indices and outputs before later stops remain covered. Policy tags select existing code; no new runtime traversal or resource/history/model supplier is assumed.

Two checked inversions recover literal selected preparation/full staged list/residual and terminal-child dispatch at the original five primitive fuels. Next extract a SPECIFIED staged child position with its actual completed prefix and native/cache endpoints. Then apply existing same-position path congruence at THAT returned Core and transport aliases through the remaining tuple and SAME final output. Whole-worker all-raw alias targetc4cb44f2 remains UNPROVED; inspect allocation bounds before an unrestricted raw-variable formulation. The outer Nat proof still must attach EVERY removed event on THAT causal branch. Earlier explored siblings cannot supply this output's history.

The largest gap remains ONE finite accepted completion of the SAME original partial root under ONE compatible rho satisfying actual native domains, UF, paths, residual guards, readback, parked recompletion and EVERY removed obligation on that branch. Existing E/R histories, immediate parked-suffix kept closure and conditional one-arrow same-snapshot model remain proved. Finite invocation ancestry does not prove this joint model or accepted completion. Warm C/M meanings, Returned/mixed clauses, pending Profile closure, typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact size/count/weights/training, both rank inverses, host bounds and compiled Haskell correspondence remain in scope.

All five publication gates pass: {report['source_files']} Source inventory files, {report['direct_audit_imports']} direct Audit imports, {report['individual_reports']} explicit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} resource/component reports and {report['audited_theorems']} audited declarations. The ten new reports are THREE relation-declaration checks and SEVEN theorem reports. All prior 218 component/resource reports remain. All 6189 old non-Audit Source files and every old Audit byte are preserved. New modules use default limits; serial jobs use 8 GiB and zero swap; no sorryAx or nonstandard axiom passes. The local visitor type-argument repair, Bool.not precedence repair and precompiler rejected digest are preserved; failed modules receive no theorem credit. No Haskell source or runtime change or reachable-source defect is claimed. Every future Haskell fix must be recorded in FINDINGS.md. Goal ACTIVE; origin/formalize publication remains explicitly authorized.'''
request = {
    'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review',
    'post_type': 'note',
    'request_id': str(uuid.uuid4()),
    'content': {'title': 'Concrete indexed eager invocation ancestry is checked; joint branch completion remains open', 'text': text},
    'metadata': {
        'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'concrete_indexed_invocation_relation_and_producer_proved': True,
        'same_original_captured_witnesses_have_invocation_trace': True,
        'every_staged_position_extraction_proved': False,
        'all_raw_alias_worker_transport_proved': False,
        'all_causal_removed_events_attached_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False,
    },
}
path = work / 'current-board-indexed-invocation-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
