from pathlib import Path
import json
import uuid

work = Path(__file__).parent
public = work.parent / '20261117-all-outer-held-publication'
report = json.loads((public / 'checked.json').read_text())
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert len(report['checks']) == 5 and report['all_history9374_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
text = f"""Checked Source {code}. The original full9374 theorem is proved: after one authentic parked clear, every later outer entry on the SAME indexed formalized eager output branch has HeldFragmentHistory from the immediate post-clear anchor. The public theorem internally constructs the actual tail OutputHistory. Genuine depth induction joins zero, parked, narrowed-right, opaque and captured callback cases. The captured case uses the SAME literal completed-tuple Current/Held return. The actual callback seed, mass, finalizer, false recordTypes call, truthful decision and suffix index remain. No future history/model/resource supplier, Canonical premise, larger runtime fuel or replacement engine is added. Every original work/depth budget and earlier output before a later stop remains covered.

The original public theorem declaration, shared5e48 predicate and21c4 history definitions remain exact. Only the obsolete OPEN status comment was removed in normal Source. Private annotations and mode conversions are recorded honestly; all first headers and failed checks remain. Owner diagnostics17,10,3,2 then PASS; the proof cap stayed200000. The final local resource alias and callback-equality repairs introduce no assumption.

A second public source theorem derives original marker/fullU/fullU staging and the SAME child-zero invocation, remaining U/U tail, and conditional terminal winner from the SAME accepted construction/build/stored-U and one actual selected trace. Its own preparation is obtained from that trace. An unjustified callerHeap=older unfolding heap premise was REMOVED, preserving actual producing-row prefixes that grow native storage. The source module passes strict default limits. Native marker semantic context at the later reader remains a genuine separate resource cut; this is provenance, not assignment existence.

The role audit pins the exact CurrentConstruction-to-CurrentContext-to-stored-U catalog link. That current escaped catalog excludes both arrow names; arbitrary catalogs need not. TypeFragment.arrow requires a literal marker child, while terminal dispatch can store a marker hole. Finalize preserves the supplied fragment. TerminalMarkerDemand only restricts assignments already satisfying its returned state. Actual source occurrence-to-class role provenance, class consistency and role-safe stored equations sufficient for ONE typed/marker evaluator remain OPEN. Native-domain truth, guards, actual dependency order/compatibility and preservation through ordered recompletion must all hold under ONE assignment for the SAME original emitted root and EVERY obligation on its causal branch. Separate existential witnesses and sibling histories cannot be spliced.

All FIVE public gates pass: {report['source_files']} Source files, {report['direct_audit_imports']} Audit imports, {report['individual_reports']} explicit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} resource/component reports and {report['audited_theorems']} audited declarations. Two new public theorems, nine private proof components, one new module; no new relation reports. All6233 old non-Audit/non-owner sources and the ENTIRE2129411-byte old owner block remain exact. All217 prior owner probes and all136 original probes remain. Public imports never access private names across modules. Serial8GiB/zero swap/default new-module limits/original2M old limits; no sorryAx/nonstandard axioms. No Haskell source changed. EVERY future Haskell fix must be in FINDINGS.md. Warm C/M/Returned/mixed/Profile, full APIs/typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, host bounds and compiled Haskell correspondence remain in scope. Goal ACTIVE; formalize push authorized."""
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Original held-history theorem and actual source arrow provenance are checked', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'new_public_theorem_reports': 2, 'new_private_component_reports': 9, 'new_modules': 1,
        'all_history9374_proved': True, 'public9374_theorem_declaration_byte_exact': True,
        'historical_open_comment_removed': True, 'shared5e48_predicate_byte_exact': True,
        'original_source_arrow_staged_provenance_proved': True,
        'actual_source_type_marker_role_preservation_proved': False,
        'actual_source_type_role_and_dependency_order_produced': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-held-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
