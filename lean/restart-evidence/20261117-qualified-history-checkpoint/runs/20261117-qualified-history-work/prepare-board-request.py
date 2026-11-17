from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = root / 'lean/restart-evidence/20261117-qualified-history-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['sorryAx'] and not x['nonstandard_axioms'] and not x['diagnostics'] for x in report['checks'])
assert report['whole_worker_all_raw_aliases_proved']
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
text = f"""Checked Source {code}. The actual indexed outer history now internally gains Canonical and Total at its recorded input/prefix/candidate/preparation/row-return/finalizer/callback cuts, plus validity of each actual bucket, from ONLY initial Canonical+Total. The three original public headers and mutual definitions remain exact. Consumers must eliminate ONE qualified derivation for joint hidden fields; a Prop proof index does not identify constructor data. The original all-budget indexed worker, alias and output preservation results remain.

One HEAD parked-clear export retains original removed bucket, literal clear, native and alias observations, immediate InputsPending/Avoids/isolation and SAME actual continuation/output index. Its worker-facing Packet+Canonical+chosen wrapper derives past Ready/PendingReferences/IncomingAvoid and history internally. An audit found immediate tail Packet/true-decision transport ALREADY available from continuing-prefix CurrentPrefixFacts, original Packet+Fits+Heap and exact Restart singleton; no new theorem credit is claimed for that audit. Packet at arbitrary hidden selected/captured cuts still needs actual phase receipts.

The new concrete nested event ledger and genuine mutual producer retain every actual own preparation, chosen child, remaining tuple, residual finish and atomic shallow dispatch cut, with exact staged positions/native/cache/output/callback indices. The actual eager producer derives its trace internally. A second genuine mutual induction proves EVERY event AuthenticEvent, and the actual wrapper returns that SAME ledger/authenticity/whole block/index decomposition jointly. Completed sibling prefixes supply native provenance; unrelated sibling enum events are excluded. Literal-operation authenticity is not semantic Holds, native membership or guard truth; outer continuation attachment remains necessary.

Ordered arrow recompletion now permits targets in EARLIER owner UF classes. One finite induction constructs ONE assignment satisfying UF, ALL stored equations and EVERY bucket, preserving kept targets and earlier buckets. Target order, distinct pending owners, dependency closure and same-position UF compatibility remain explicit inputs. TypeFragment grammar/fill and genuine every-fuel evaluator induction now derive TypeIn from past stored syntax and a typed base. A combined theorem internally builds the original frontier+1 evaluator with var1 default, derives initial target typing at THAT SAME evaluator, then constructs the ordered joint assignment. No current-model/equation/future targetTypeIn supplier is assumed. Actual source preservation of marked syntax and order, native domains and guards remain open.

The source-grounded zero-child original-U row base also proves exact same literal fragment and TypeIn under EVERY assignment. Native normalization meaning, TargetQuery intersection meaning and exact stored-U language characterization ALREADY exist and must be reused. The remaining nonleaf/lazy source gap is typing the SAME reconstructed final target after Finalize erases its native handle; pending-only native invariants do not type that expanded slot. Generic Haskell stop/truncation APIs explicitly do not promise a finite accepted completion. This does not settle the SAME-original accepted source/root/noStop target. No reachable accepted-source counterexample or Haskell defect is claimed.

All FIVE gates pass: {report['source_files']} Source files, {report['direct_audit_imports']} Audit imports, {report['individual_reports']} explicit reports, {report['independent_reports']} independent, {report['resource_and_component_probes']} resource/component reports, {report['audited_theorems']} audited declarations. Fifteen new theorem reports in nine modules and ten declaration checks. All6216 old non-Audit Source files, old Audit bytes, owner and all272 prior resource/component reports remain exact;208 owner/136 original probes preserved. Serial8GiB/zero swap/default new limits/original2M owner limit; no sorryAx/nonstandard axioms. Failures and scope/private-query/fill/provenance repairs remain saved without proof credit. No Haskell source changed; EVERY future fix must be in FINDINGS.md. Full causal native/guard/history completion, warm C/M/Returned/mixed/Profile, full APIs/typing/depth/completeness/preprocessing/LPO/order/multiplicity/lazy demand/exact sizes/count/weights/training/both rank inverses/host bounds/compiled Haskell correspondence remain open. Goal ACTIVE; formalize push authorized."""
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Qualified causal histories, authentic nested ledgers and typed ordered recompletion are checked', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'original_c4cb44f2_header_preserved': True, 'whole_worker_raw_alias_transport_proved': True,
        'mutual_invocation_alias_composition_proved': True, 'same_child_entry_roots_producer_proved': True,
        'same_selected_child_path_aliases_proved': True,
        'actual_indexed_outer_history_producer_proved': True,
        'whole_real_eager_canonicality_proved': True,
        'independent_arrow_batch_joint_assignment_proved': True,
        'general_owner_as_target_joint_recompletion_proved': False,
        'qualified_recorded_outer_entries_proved': True,
        'nested_ledger_produced_and_every_event_authentic': True,
        'ordered_pending_owner_joint_assignment_proved': True,
        'same_evaluator_typing_internally_derived_from_stored_syntax': True,
        'actual_source_type_role_and_dependency_order_produced': False,
        'all_causal_removed_events_attached_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-qualified-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
