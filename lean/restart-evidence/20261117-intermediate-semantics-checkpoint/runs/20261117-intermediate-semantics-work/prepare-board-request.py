from pathlib import Path
import json
import uuid

work = Path(__file__).parent
public = work.parent / '20261117-intermediate-semantics-publication'
report = json.loads((public / 'checked.json').read_text())
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert len(report['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] and not item['diagnostics']
           and not item['sorryAx'] for item in report['checks'])
text = f"""Checked Source {code}. Genuine original-work induction now derives the actual completed tuple's Current, Origin and FrameLedger at the SAME literal callback return. Tuple/child/row cases preserve the original frame, fragments, native caller, queries, cache and output indices. A wrapper derives its resource depth IH internally from the existing all-depth result. A consumer eliminates ONE returned Current witness and derives HeldFragmentHistory at THAT SAME cache from genuine PAST root-to-scope history and original bucket avoidance. It assumes no future resource/history supplier. The public CapturedTupleInputs export names the existing receipt and derives selected-return, actual-finalizer and literal false-recordTypes callback Packets with full memos/query equality, Frame/RenderStable, Fits/Heap/mass/store/root at original fuels. It does not produce TupleInputs by itself; the checked private literal-invocation proof supplies that forward step.

Source terminal-marker demand is checked at its original accepted-source/stored-U premises and actual terminal singleton call. The SAME returned hole winner has its actual UF path, pending native handle and closed marker readback; original terminal targets alias it. EVERY assignment satisfying THAT returned state gives the winner the literal marker. This restricts satisfying assignments; it proves no assignment existence. The original unfolded-source row bridge derives actual Top own preparation and distinguishes catalog rows from the genuine arrow. Only the genuine arrow yields staged marker zero. Top retains inherited descended demands. Catalog names can equal the arrow name, so symbol equality alone cannot classify a row. Type and marker roles are not globally disjoint for every catalog. A pure guarded-to-eager invocation transport retains all literal callbacks, fuels, endpoints and indices when all original inputs have lower height.

The original full9374 history-protection theorem remains OPEN. Its first header and mutual definitions are exact. A new low-level module contains those definitions; its reports are declaration checks, not runtime admission proofs. Base, opaque, captured, successor and original-public assembly drafts are frozen UNCOMPILED. The original full9374 assumes no Canonical, so the newer qualified joint ledger cannot be substituted by adding that premise. Current checked tuple cuts are components, not a proof of every historical cut.

The public-boundary audit reuses actual noStop output control: every emitted modeled output has metadata none and next done; fresh depth exhaustion emits nothing while earlier outputs before later stops remain covered. A rootPartial observation alone does not prove emission. The accepted empty-library/zero-size example is not a source counterexample: existing modeled initializer theorem proves no outputs at its exact identity-narrowing specialization, and Haskell rejects EmptyNode after narrowing before expansion/readback. The public API harness is UNEXECUTED. No Haskell execution or reachable-source defect is claimed.

Largest gap remains ONE finite accepted completion of the SAME original emitted partial root under ONE compatible assignment satisfying native domains, proper paths, UF aliases, residuals, readback and EVERY removed/parked obligation on THAT causal branch. Finish full9374 admission, source Type/Marker role transport through lazy allocation/intersection/UF/finalization, semantic interpretation of atomic cuts, actual class order and target compatibility. Reuse existing native normalization/query/stored-U meanings and ordered conditional ONE-assignment recompletion. Do not splice sibling histories or separate existential models.

All FIVE gates pass: {report['source_files']} Source files, {report['direct_audit_imports']} Audit imports, {report['individual_reports']} explicit reports (631 standard/6 free), {report['independent_reports']} independent, {report['resource_and_component_probes']} resource/component reports and {report['audited_theorems']} audited declarations. Six new public theorem reports, nine private proof-component reports and two relation declaration reports; five new normal modules plus the extended owner. Public reports do not access private names across modules. All6228 old non-Audit/non-owner sources remain exact. The ENTIRE2050962-byte old owner remains one exact contiguous block after three ordinary imports; every old proof body/limit and all prior probes remain. Serial8GiB/zero swap/default new limits/200000 new-owner limits/original2M old limits. No sorryAx/nonstandard axioms. Failures and repairs remain saved without credit. No Haskell source changed; EVERY future fix must be in FINDINGS.md. Warm C/M/Returned/mixed/Profile, full typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, host bounds and compiled Haskell correspondence remain in scope. Goal ACTIVE; formalize push authorized."""
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Exact captured callback cuts and source marker restrictions are checked', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'new_public_theorem_reports': 6, 'new_private_component_reports': 9,
        'new_relation_declaration_reports': 2, 'new_modules': 5,
        'literal_callback_current_cut_proved': True, 'literal_callback_held_cut_proved': True,
        'source_marker_satisfying_assignment_restriction_proved': True,
        'original_source_unfolded_row_top_and_arrow_input_proved': True,
        'same_guarded_eager_invocation_transport_proved': True,
        'all_history9374_proved': False, 'full9374_candidate_frozen_uncompiled': True,
        'actual_source_type_role_and_dependency_order_produced': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-intermediate-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
