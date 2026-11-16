from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = root / 'lean/restart-evidence/20261116-invocation-alias-composition-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['sorryAx'] and not x['nonstandard_axioms'] and not x['diagnostics'] for x in report['checks'])
assert report['whole_worker_all_raw_aliases_proved']
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
text = f"""Checked Source {code}. The EXACT original whole-worker raw-alias target c4cb44f2 is proved. Every actual eager-worker output retains every entry raw SameClass pair at THAT output cache. All original parameters, resource premises, supplied work/recursive fuels, stopping behavior and outputs before later stops remain. Genuine depth induction uses the indexed ACTUAL producing row and SAME captured callback input/output occurrence. It does not infer invocation identity from equal output values or splice sibling histories. No future alias, callback-correctness, resource-history or model supplier is added. A public specialization handles an arbitrary actual restart decision at its entry cache without Packet/resource premises, using the same depth proof.

The supporting mutual child/tuple/selected invocation proofs retain all raw aliases at the same completed return. Own preparation/residual finish keep forests. The configured prefix law retains all SIX independent primitive fuels and actual checked/candidate cores. Captured Finalize and literal singleton false recordTypes preserve aliases. The stronger captured restart producer retains all original witness fields and adds input-alias transport for THOSE SAME fields. Initial Total propagates through actual prior children and jointly produces Roots at the chosen child's authentic entry. The selected child path theorem uses the original staged[position], actual preparation, input Total and valid parent bucket to carry same-position aliases through the SAME remaining tuple and residual finish to selected return. Those input invariants remain explicit. Local alias laws add no Total/Safe/allocation-bound supplier; the path theorem still has its genuine input validity premises.

The main semantic gap remains ONE finite accepted completion of the SAME original emitted partial root under ONE compatible assignment satisfying native domains, UF, paths, residual guards, readback and EVERY removed/parked obligation on THAT causal branch. EVERY historical removed occurrence still needs its authentic final-output attachment. Earlier explored sibling histories do not belong to this output. Whole-worker E/R histories, actual immediate parked-suffix kept closure and conditional same-snapshot ONE-arrow recompletion remain proved. Whole-worker alias preservation and finite invocation ancestry do not construct a joint accepted model. The original stored-U language and exact TypeIn characterization are already proved at their source/build/top-guard premises. Authentic membership of the final causal raw-target values in that language (or an admitted rigid domain), target compatibility and native/guard meanings remain open at this boundary. DonePendingTypes admits already typed witnesses and does not type reconstructed expanded targets. Warm C/M, Returned/mixed clauses, pending Profile closure, typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, host bounds and compiled Haskell correspondence remain in scope.

All FIVE gates pass: {report['source_files']} Source inventory files, {report['direct_audit_imports']} direct Audit imports, {report['individual_reports']} explicit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} resource/component reports and {report['audited_theorems']} audited declarations. Sixteen new theorem reports in eight modules. All previous237 resource/component reports, 208 owner reports and ALL136 original probes remain. All6198 old non-Audit Source files and entire resource owner remain exact; all old Audit bytes remain after eight ordinary acyclic imports. Serial8GiB/zero swap, unchanged default new-module limits and original2M owner limit; no sorryAx/nonstandard axiom. All failed checks and exact recursor/scope/projection/explicit-argument/dependent-guard repairs are preserved without failed-module credit or linter suppression. No Haskell/runtime change or reachable-source defect is claimed. EVERY future Haskell fix must be in FINDINGS.md. Goal ACTIVE; formalize publication remains explicitly authorized."""
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Original eager worker raw-alias transport and selected child paths are checked', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'original_c4cb44f2_header_preserved': True, 'whole_worker_raw_alias_transport_proved': True,
        'mutual_invocation_alias_composition_proved': True, 'same_child_entry_roots_producer_proved': True,
        'same_selected_child_path_aliases_proved': True,
        'all_causal_removed_events_attached_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-invocation-alias-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
