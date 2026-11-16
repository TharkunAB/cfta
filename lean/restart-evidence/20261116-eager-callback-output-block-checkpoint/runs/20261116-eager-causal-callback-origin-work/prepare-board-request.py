from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = root / 'lean/restart-evidence/20261116-real-eager-callback-output-block-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5 and all(x['exit'] == 0 and not x['sorryAx'] and not x['nonstandard_axioms'] for x in report['checks'])
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
text = f'''Checked Source {code}. The five-module chain now retains whole indexed output blocks through the REAL eager child policy. scan_output_block_origin retains the producing row, complete prefix and native endpoint, exact local index/offset, and full outputs=earlier++rowOutputs++later even when the suffix stops. Generic visitChildren uses genuine list induction. Actual eager_child_callback_blocks uses genuine Nat.strongRecOn ordinary height; guarded lower children use the IH and actual shallow fallback. Its header assumes no future callback-policy law/history/model/selector/resource supplier. The actual singleton SelectedPreparation/nonterminal producer retains distinct decoded/prepared values and reaches the indexed real producing row.

The EXACT frozen real_eager_captured_output_callback_restart_origin header2a0d5ae8 is proved at original workFuel/recursiveDepth. Each indexed real captured-row output has successful literal Finalize and singleton false recordTypes witnesses, the SAME recur call, its WHOLE emitted block and exact local index/offset. This is an EXTENSIONAL restart-block witness. It does not record an indexed executed child invocation, so it must not be used alone to associate a historical removed occurrence with a child. The new owning GHC-style Note states that boundary and related modules refer to it. Only comments were added beyond frozen checked definitions/headers/proofs.

Next: internally PRODUCE an indexed invocation derivation for THOSE SAME witness fields alongside genuine CPS/list/height induction, then attach all causal removed events through genuine smaller-depth recursion. CapturedCallbackInvocationAt in the frozen audit is explicitly UNDEFINED/UNPROVED design, not a compiled relation, axiom or supplied premise. Constructors must retain literal prepare, staged child position/completed prefix, chosen row prefix/index, selected-return frame, fallback singleton, Finalize and false callback. ActualSourceOrigin/ActualFrameLedger retain authentic past facts but lack output occurrence; a separate Origin conjunction with block equality is insufficient. Sibling scans reuse captured enum state, so earlier explored sibling clears/aliases cannot supply this output's history. Another audit finds no whole-worker ALL-raw-alias monotonicity theorem: local frame/RenderStable/terminal receipts are narrower. Exact original-budget all-raw alias targetc4cb44f2 remains UNPROVED; child-to-final use also needs genuine CPS incidence.

Largest gap remains ONE finite accepted completion of the SAME original partial root under ONE compatible rho satisfying native domains/guards, UF, stored equations and EVERY removed/parked obligation on THAT causal branch. Old whole-worker E/R, actual parked-suffix kept closure and conditional one-arrow same-snapshot recompletion remain proved. Target compatibility/typing, final aliases, indexed causal history and native/guard meanings still need authentic producers under ONE rho. ResourceHistory.render_sound remains valid at its explicit history/residual boundary. Warm C/M meanings, Returned/mixed clauses, pending Profile closure, full typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, host bounds and compiled Haskell correspondence remain in scope.

All FIVE gates pass: {report['source_files']} Source inventory files, {report['direct_audit_imports']} direct Audit imports, {report['individual_reports']} explicit reports ({report['checks'][-1]['axiom_groups']} standard/{report['checks'][-1]['axiom_free_reports']} free), {report['independent_reports']} independent, {report['resource_and_component_probes']} resource/component reports ({report['owner_resource_probes']} old owner incl ALL136 original +10 new components), {report['audited_theorems']} audited declarations. Strict reports216 standard/2 free. Default limits for new modules; original2M owner limit; serial8GiB/zero swap; pins unchanged; no sorryAx/nonstandard axiom. All6184 old non-Audit Source files and entire owner byte-exact; old Audit preserved after five ordinary acyclic imports. Counts are not full API coverage/completion. All missing-import/reserved-name/match-reduction/section-instance failures and exact repairs are preserved, with no failed-module credit and no linter suppression. No Haskell/runtime change or reachable-source defect is claimed. EVERY future Haskell fix must be in FINDINGS.md. Goal ACTIVE; origin/formalize publication explicitly authorized.'''
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337', 'username': 'mcfta-lean-review',
    'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Real eager callback output-block origins are checked; indexed invocation history remains open', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_and_component_probes': report['resource_and_component_probes'],
        'audited_declarations': report['audited_theorems'], 'public_gates': 5,
        'genuine_eager_height_callback_block_induction_proved': True,
        'exact_real_captured_restart_output_block_proved': True,
        'indexed_executed_invocation_trace_proved': False, 'all_raw_alias_worker_transport_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-eager-block-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
