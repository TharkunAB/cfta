from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = root / 'lean/restart-evidence/20261117-final-output-causal-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['sorryAx'] and not x['nonstandard_axioms'] and not x['diagnostics'] for x in report['checks'])
assert report['whole_worker_all_raw_aliases_proved']
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
text = f"""Checked Source {code}. Every emitted occurrence of the actual bounded eager resume now has an indexed outer causal history at its original supplied work and recursive budgets. The exact first-frozen 80008813 public header is retained. Genuine depth induction records the actual selected prefix, common preparation, producing row and whole output block, SAME indexed child/callback invocation and SAME recursive suffix index. Earlier outputs before a later stop remain covered. No future history, model or invariant supplier is added. This proves operational ancestry; extraction and semantic truth of EVERY removed/deferred obligation remain open.

The actual worker and arbitrary literal restarts preserve Canonical storage from ONLY initial Canonical. Literal prefix and preparation observations derive checked/candidate Canonical, entered Total and bucket validity at the original independent fuels. Actual shared ChildDispatch and mutual invocation laws retain Canonical at their same completed returns. Canonical describes valid trie representation, not satisfaction of constraints. The final-path theorem carries original indexed same-position aliases to the SAME final output using the SAME captured witnesses, with its genuine initial Total/bucket validity conditions. Proper-path descent derives the actual staged child and exact duplicate-sensitive descendant index. The shallow footprint records actual lazy allocation: ordinary nodes store the full bucket, Mu/Union allocation stores an empty bucket, and fresh-owner lookup still requires past counter/storage alignment in its conclusion.

A finite INDEPENDENT arrow-bucket batch now receives ONE assignment satisfying UF, ALL stored equations and every bucket, preserving kept targets and earlier buckets. Actual target typing, same-position compatibility, pairwise distinct owner classes and ONE dependency-closed kept set excluding every owner remain explicit inputs. Owners used as other buckets' targets are outside this theorem. Two checked finite-term cycle laws show why general recompletion needs equality-class dependency control, even when the raw graph is acyclic. These mathematical boundaries are not reachable-source or Haskell defects.

Largest gap: ONE finite accepted completion of the SAME original emitted partial root under ONE compatible assignment satisfying actual native domains, paths, UF, residual guards, readback and EVERY removed/parked obligation on THAT branch. Final causal-target TypeIn/native membership after expansion, all-event semantic coverage and general dependent-owner recompletion remain open. The exact stored-U language characterization is already proved; DonePendingTypes only admits already typed witnesses. Warm C/M meanings, Returned/mixed clauses, pending Profile closure, full typing/depth/completeness, both preprocessing/LPO directions, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, host bounds and compiled Haskell correspondence remain in scope.

All FIVE gates pass: {report['source_files']} Source files, {report['direct_audit_imports']} direct Audit imports, {report['individual_reports']} explicit reports, {report['independent_reports']} independent reports, {report['resource_and_component_probes']} resource/component reports and {report['audited_theorems']} audited declarations. Nineteen new theorem reports in ten modules; two additional history-relation declaration checks. All6206 old non-Audit Source files, old Audit bytes and entire resource owner remain exact; all253 prior component reports,208 owner reports and136 original probes remain. Serial8GiB/zero swap; default new-module limits; unchanged2M owner limit; no sorryAx/nonstandard axiom. Failed checks and exact repairs remain saved without theorem credit. No Haskell/runtime source changed and no reachable-source defect is claimed. EVERY future Haskell fix must be in FINDINGS.md. Goal ACTIVE; formalize publication remains authorized."""
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Indexed causal histories, canonical storage and independent batch recompletion are checked', 'text': text},
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
        'all_causal_removed_events_attached_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-causal-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
